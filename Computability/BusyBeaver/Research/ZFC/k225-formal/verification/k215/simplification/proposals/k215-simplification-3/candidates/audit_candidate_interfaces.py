#!/usr/bin/env python3
"""Read-only independent finite audit. No received modules are imported or run.
This is ordinary finite checking, not a Lean/Rocq kernel certificate.
"""
import argparse, hashlib, itertools, json, pathlib
ROOT=pathlib.Path(__file__).resolve().parent
if not __debug__:
    raise SystemExit("Assertions must be enabled; do not use -O or -OO.")
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output",type=pathlib.Path,help="Optional path for the recomputed JSON; the packet is read-only by default.")
parser.add_argument("--expected",type=pathlib.Path,help="Optional archived result to compare against, in addition to recomputing.")
args=parser.parse_args()
INPUTS=ROOT/"inputs"
manifest_bytes=(ROOT/"INPUTS.json").read_bytes()
assert hashlib.sha256(manifest_bytes).hexdigest()=="b89235c06c23c3b4753062ade463459bb7951445491780583e26fe71ebbe621f", "Input provenance/manifest changed"
manifest=json.loads(manifest_bytes)
pinned={x["path"]:x for x in manifest["files"]}
def read_input(path):
    data=(INPUTS/path).read_bytes()
    pin=pinned[path]
    assert len(data)==pin["bytes"] and hashlib.sha256(data).hexdigest()==pin["sha256"], path
    return data
for path in pinned:
    read_input(path)
COMMIT='613f9cf28ac36eaa929f7ef909b0eb7905facc5d'
def sha(b): return hashlib.sha256(b).hexdigest()
def table(data):
    rows={}; start=None
    for line in data.decode().splitlines():
        if line.startswith('#! start '): start=int(line.split()[-1])
        if not line or line.startswith('#'): continue
        q,r,w,d,t=line.split(); key=(int(q),int(r)); assert key not in rows
        rows[key]=(int(w),1 if d=='R' else -1,int(t))
    states={q for q,r in rows}; assert set(rows)=={(q,r) for q in states for r in [0,1]}
    halt={t for w,d,t in rows.values()}-states; assert len(halt)==1
    return rows,start,next(iter(halt))
def source_stats(data):
    sites=json.loads(data); leaves={x[0]:(x[1],x[2]) for x in sites}; seen=set()
    assert len(leaves)==len(sites)
    def node(p):
        k=('leaf',)+leaves[p] if p in leaves else ('node',node(p+'0'),node(p+'1'))
        seen.add(k); return k
    node('')
    return {'leaves':len(sites),'distinct_subtrees':len(seen),'max_depth':max(len(x[0]) for x in sites),'address_sum':sum(len(x[0]) for x in sites)}
def serial_diff(a,b):
    return [{'row':list(k),'old':a.get(k),'new':b.get(k)} for k in sorted(set(a)|set(b)) if a.get(k)!=b.get(k)]
base_b=read_input('original/k215.native.tm'); base,bs,bh=table(base_b)
base_dense=read_input('original/k215.tm'); base_sites=read_input('original/sites215.json')
assert sha(base_b)=='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
assert sha(base_dense)=='fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
cm_b=read_input('CM215/marker215.native.tm'); cm,cs,ch=table(cm_b)
assert sha(cm_b)=='e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252'
assert read_input('CM215/sites.json')==base_sites
assert set(base)==set(cm) and bs==cs==0 and bh==ch==254
phi=lambda q: 52 if q==176 else q
for (q,r),(w,d,t) in base.items():
    if q not in [52,176]: assert cm[q,r]==(w,d,phi(t))
assert base[52,1]==base[176,1]==cm[52,1]
incoming={str(t):[[q,r,*wd] for (q,r),(*wd,z) in base.items() if z==t] for t in [52,176,156]}
# Strengthened one-step inductive invariant, rather than reasoning by backward histories.
def inv(q,tape,h):
    return (q!=52 or tape[h-1]==1) and (q!=156 or tape[h+1]==1) and (q!=176 or tape[h]!=0 or tape[h-1]==0)
count=0
for q in sorted({q for q,r in base}):
    for bits in itertools.product([0,1],repeat=5):
        tape=dict(zip(range(-2,3),bits))
        if not inv(q,tape,0): continue
        w,d,t=base[q,tape[0]]; tape[0]=w
        assert inv(t,tape,d), (q,bits,t)
        count+=1
assert all(inv(0,dict(zip(range(-2,3),bits)),0) for bits in itertools.product([0,1],repeat=5))
def localrun(m,q,tape,n):
    h=0; tr=[]; tape=dict(tape)
    for _ in range(n):
        assert h in tape,'unspecified cell read'
        r=tape[h]; w,d,t=m[q,r]; tr.append([q,h,r,w,d,t]); tape[h]=w;h+=d;q=t
    return [q,h,tape],tr
blocks=[]
for q,left in [(52,1),(176,0)]:
    a,ta=localrun(base,q,{-1:left,0:0},1)
    b,tb=localrun(cm,phi(q),{-1:left,0:0},3)
    assert a==b
    blocks.append({'source_state':q,'context':{-1:left,0:0},'old_trace':ta,'new_trace':tb,'endpoint':a})
# Literal renaming, not just hash match, connects native original to verified dense artifact.
mapdata=json.loads(read_input('original/canonicalization.json')); ren={int(k):v for k,v in mapdata['native_to_canonical'].items()}
dense,ds,dh=table(base_dense)
assert { (ren[q],r):(w,d,ren[t]) for (q,r),(w,d,t) in base.items()}==dense
assert ren[bs]==ds and ren[bh]==dh
inventory=[]
def add(name,nb,sb,db=None):
    t,s,h=table(nb)
    inventory.append({'name':name,'native_sha256':sha(nb),'dense_sha256':sha(db) if db else None,'source_sha256':sha(sb),'working_states':len(t)//2,'rows':len(t),'start':s,'halt':h,'native_row_delta_from_original':len(serial_diff(base,t)),**source_stats(sb)})
add('original',base_b,base_sites,base_dense)
add('CM215',cm_b,read_input('CM215/sites.json'),read_input('CM215/marker215.tm'))
for name,stem,sites in [('context215','k215-context','sites215.json'),('shallow215','k215-shallow','sites-shallow.json')]:
    add(name,read_input(name+'/'+stem+'.native.tm'),read_input(name+'/'+sites),read_input(name+'/'+stem+'.tm'))
add('R41',read_input('R41/k215r.native.tm'),read_input('R41/sites215r.json'),read_input('R41/k215r.tm'))
add('ST215',read_input('ST215/st215.native.tm'),read_input('ST215/st215.sites.json'),read_input('ST215/st215.tm'))
add('common-pop215',read_input('common-pop215/candidate.native.tm'),read_input('common-pop215/sites.json'),read_input('common-pop215/candidate.tm'))
result={'status':'FINITE_INTERFACE_AUDIT_PASS','scope':'Finite literal rows, source metrics, strengthened marker invariant and local blocks only. Not a new kernel check or whole consistency proof.','original_commit':COMMIT,'native_dense_bijection_checked':True,'cm_delta':serial_diff(base,cm),'cm_incoming':incoming,'cm_strengthened_invariant_accepted_neighborhoods':count,'cm_local_blocks':blocks,'inventory':inventory}
encoded=json.dumps(result,indent=2)+'\n'
if args.expected:
    assert json.loads(encoded)==json.loads(args.expected.read_text()), "Recomputed result differs from archived result"
if args.output:
    args.output.write_text(encoded)
print(encoded,end='')
