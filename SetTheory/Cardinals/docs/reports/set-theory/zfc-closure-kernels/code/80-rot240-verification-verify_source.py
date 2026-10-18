"""Whole-source context and literal blank proof for the second QT rotation.

All incoming guards are enumerated as finite source-graph data. The only
unbounded arithmetic ingredient is natural induction on the consumed R6.
This checker establishes executable mathematical evidence, not a kernel proof.
"""
from pathlib import Path
import json,hashlib,sys,collections,argparse,os
if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions required; disable -O and PYTHONOPTIMIZE')
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--package-root',type=Path,help='Package containing reference/ and machines/; normally auto-detected')
parser.add_argument('--output-dir',type=Path,help='Evidence output directory; defaults to package evidence/')
args=parser.parse_args()
if args.package_root is not None:
    PACKAGE=args.package_root.resolve()
else:
    candidates=[p for p in Path(__file__).resolve().parents
                if (p/'reference/baseline241_old.tm').is_file() and (p/'machines/sites_logical.json').is_file()]
    if not candidates:parser.error('Cannot locate package; pass --package-root')
    PACKAGE=candidates[0]
OUT=(args.output_dir.resolve() if args.output_dir else PACKAGE/'evidence')
OUT.mkdir(parents=True,exist_ok=True)
OLD_TABLE=PACKAGE/'reference/baseline241_old.tm'
OLD_SITES=PACKAGE/'reference/baseline_sites.json'
NEW_TABLE=PACKAGE/'reference/rotated241_old.tm'
NEW_SITES=PACKAGE/'machines/sites_logical.json'
PINS={
    OLD_TABLE:'1fa8526c3c971d5a48868599eaed890f614c5a79256e51622d3e32a64229f3a3',
    OLD_SITES:'3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4',
    NEW_TABLE:'88a1f42b01b7e2b4bf29bc1b3819b78f1e7a17cefaefbc003654f2f5cc202c2f',
    NEW_SITES:'74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d',
}
def check_pins():
    for path,digest in PINS.items():
        assert hashlib.sha256(path.read_bytes()).hexdigest()==digest,('Changed pinned input',str(path))
check_pins()
roots=['11101001001011000011','1110100100101110011','1110100101100011','111110011']
old=json.loads(OLD_SITES.read_text());new=json.loads(NEW_SITES.read_text())
def source(ss):
 leaf={p:(op,r)for p,op,r in ss};assert len(leaf)==len(ss)
 pre={p[:i]for p in leaf for i in range(len(p))}
 assert len(pre)==len(leaf)-1 and not pre&leaf.keys()
 assert all(p+b in pre or p+b in leaf for p in pre for b in'01')
 def contract(p):
  assert p in pre or p in leaf
  while p not in leaf:p+='0'
  return p
 def inc(p):return p[:p.rindex('0')]+'1' if'0'in p else''
 def strip(p,b,k):
  while k and p:k-=p[-1]==b;p=p[:-1]
  return p
 def dst(p,positive=False):
  op,r=leaf[p]
  if op=='CH':return None
  if op=='CI' or op=='CD' and positive:q=inc(p)
  elif op in ('CD','CB'):q=inc(strip(p,'0',r if op=='CB' else 1))
  else:assert op=='CC';q=strip(p,'1',r)
  return contract(q)
 return leaf,contract,dst
ol,oc,od=source(old);nl,nc,nd=source(new)
oldlocal={p+q for p in roots for q in['00','010','011','1']}
newlocal={p+q for p in roots for q in['0','10','11']}
assert set(ol)-oldlocal==set(nl)-newlocal
assert all(ol[p]==nl[p]for p in set(ol)-oldlocal)
assert len(ol)==6459 and len(nl)==6455
assert sum(op=='CH'for op,r in ol.values())==sum(op=='CH'for op,r in nl.values())==1
boundary={oc(p):nc(p)for p in roots}
outer_checks=0;incoming=collections.defaultdict(list);local_proofs=[]
for p in sorted(set(ol)-oldlocal):
 for positive in([False,True]if ol[p][0]=='CD' else[False]):
  a,b=od(p,positive),nd(p,positive)
  if a in oldlocal:
   assert a in boundary,('outside enters old interior',p,positive,a)
   incoming[a].append([p,positive])
  if b in newlocal:assert b in boundary.values(),('outside enters new interior',p,positive,b)
  assert boundary.get(a,a)==b,('outside edges differ',p,positive,a,b)
  outer_checks+=1
for p in roots:
 a,b,c,d=p+'00',p+'010',p+'011',p+'1'
 e,f,g=p+'0',p+'10',p+'11'
 assert [ol[x]for x in(a,b,c,d)]==[('CD',6),('CI',5),('CC',2),('CI',5)]
 assert [nl[x]for x in(e,f,g)]==[('CI',5),('CD',6),('CC',2)]
 assert od(a,False)==d and od(a,True)==b and od(b)==c and od(c)==a
 assert nd(e)==f and nd(f,True)==g and nd(g)==e
 assert od(d)==nd(f,False) and od(d)not in oldlocal|newlocal
 local_proofs.append(dict(root=p,old_entry=a,new_entry=e,common_exit=od(d),outside_incoming=incoming[a],
    zero_case=dict(old_steps=2,new_steps=2,post='R5=a+1,R6=0'),
    positive_case=dict(old_steps=3,new_steps=3,recurrence='(a,b)->(a+1,b-1); b>=1'),
    induction='Both terminate for every a,b in N with R5=a+b+1,R6=0, other registers unchanged, in3b+2 source instructions.'))
assert len(local_proofs)==4
assert oc('')==nc('')
assert outer_checks==8370
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report=dict(status='SOURCE_CONTEXT_ROTATION142_PASS',old_source_sha256=sha(OLD_SITES),new_source_sha256=sha(NEW_SITES),
 old_leaves=len(old),new_leaves=len(new),old_guarded_cases=sum(2 if o=='CD'else 1 for p,o,r in old),new_guarded_cases=sum(2 if o=='CD'else 1 for p,o,r in new),outside_guarded_edges=outer_checks,
 macro_count=4,macros=local_proofs,arbitrary_registers=True,no_outside_entry_to_macro_interiors=True,halt_unchanged=True,
 global_theorem='At the empty source pointer, old and new programs halt equivalently for every natural9-register file. Compare equal files at outside leaves and corresponding macro entries. Natural induction gives finite macro exits; all surrounding guarded edges agree. No source consistency or blank-reachability premise is used.')
(OUT/'rotation142_source_proof.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

def read(p):
 t={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();t[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
 return t
bt=read(OLD_TABLE);nt=read(NEW_TABLE)
assert bt.keys()==nt.keys() and len(nt)==482
assert {k:v for k,v in nt.items()if bt[k]!=v}=={(142,0):(0,1,72),(142,1):(1,1,17)}
want={-6,176};pos=177
for value in[0,0,0,3,0,0,3,0,0]+[1]*167:
 pos+=1;want.update(range(pos,pos+value+1));pos+=value+1
q,h,ones=95,0,set();visits=collections.Counter()
for tick in range(2000001):
 if(q,h,ones)==(96,-5,want):break
 assert q!=254,'Halted before established root frame'
 b=int(h in ones);visits[q,b]+=1;w,d,q=nt[q,b]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d
else:raise AssertionError('No expected frame within construction bound')
assert tick==408941
# Independent dense dynamic-array replay, with canonical numbering.
order=[95]+sorted({q for q,b in nt}-{95});ren={q:i for i,q in enumerate(order)}|{254:241}
ct={(ren[q],b):(w,d,ren[z])for(q,b),(w,d,z)in nt.items()}
arr=bytearray(1);left=0;head=0;state=0
for t in range(tick):
 if head<left:arr=bytearray(left-head)+arr;left=head
 if head>=left+len(arr):arr.extend(bytearray(head-left-len(arr)+1))
 w,d,state=ct[state,arr[head-left]];arr[head-left]=w;head+=d
assert(state,head,{left+i for i,b in enumerate(arr)if b})==(ren[96],-5,want)
boot=dict(status='ROTATION142_EXACT_BLANK_PASS',table_sha256=sha(NEW_TABLE),working_states=241,rows=482,steps=tick,old_state=96,head=-5,marker=-6,header=176,
 logical_registers=[3,0,0,0,3,0,0,0,0],physical_registers=[0,0,0,3,0,0,3,0,0],spares_count=167,spares_values=1,ones=sorted(want),all_other_cells_zero=True,
 changed_row_visits={str(k):visits[k]for k in[(142,0),(142,1)]},two_independent_interpreters=True)
(OUT/'rotation142_boot.json').write_text(json.dumps(boot,indent=2)+'\n')
print(json.dumps({k:v for k,v in boot.items()if k!='ones'},indent=2))

check_pins()
