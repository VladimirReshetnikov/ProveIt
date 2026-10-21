"""Independent data/receipt review. Never executes or imports received programs."""
import os, sys
if sys.flags.optimize or os.environ.get("PYTHONOPTIMIZE"):
    raise SystemExit("Audit requires assertions: reject -O, -OO, and nonempty PYTHONOPTIMIZE.")
from pathlib import Path
import hashlib,json,re
BASE=Path(__file__).resolve().parent
ROOT=BASE/'extracted/K215_Checked_Simplifications_2026-10-21'
def H(b):return hashlib.sha256(b).hexdigest()
def sh(p):return H(p.read_bytes())
def read(p):return json.loads(p.read_text())
checks={}
# Whole released manifest, itself pinned to the reviewed archive bytes.
assert sh(ROOT/'SHA256SUMS')=='81b38352636ea7ec0485a5697a7de8f88b88fb25ae40e5599faff9639a59196c', 'Received manifest changed'
manifest=[]
for line in (ROOT/'SHA256SUMS').read_text().splitlines():
    digest,name=line.split(None,1);name=name.lstrip('*'); p=ROOT/name
    assert p.is_file(),name
    assert sh(p)==digest,name
    manifest.append(name)
checks['manifest']={'count':len(manifest),'all_match':True,'unlisted_files':sorted(str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file() and str(p.relative_to(ROOT)) not in manifest)}
# Compiler receipts, including explicit Coq compatibility transformation.
N=ROOT/'normalized_rocq'; receipt=read(N/'verification/result.json')
for row in receipt['sources']:
    rel=row['module']; p=N/('deps/K230/RMEquiv.rocq91.v' if rel=='deps/K230/RMEquiv.v' else rel)
    data=p.read_bytes();assert H(data)==row['delivered_sha256'],rel
    if rel=='deps/K230/RMEquiv.v':
        needle=b'From K230 Require Import RM.';assert data.count(needle)==1
        data=data.replace(needle,needle+b'\nRequire Import Compat818.')
    assert H(data)==row['compiled_sha256'],rel
for row in receipt['checks']:
    log=N/'verification/logs'/(row['name']+'.log')
    assert sh(log)==row['log_sha256'],row['name']
    assert row['exit_code']==0,row['name']
    assert log.read_text().count('Closed under the global context')==row['closed_reports']
assert sh(N/'build.py')==receipt['driver_sha256']
interface=read(N/'verification/interface-result.json')
for row in interface['checks']:
    assert sh(N/'integration'/(row['name']+'.v'))==row['source_sha256']
    log=N/'verification/logs'/(row['name']+'.log')
    assert sh(log)==row['log_sha256'];assert row['exit_code']==0
    assert log.read_text().count('Closed under the global context')==row['closed_reports']==1
assert sh(N/'complete_interface_audit.py')==interface['driver_sha256']
generic=read(N/'verification/generic-kernel-result.json');assert generic['exit_code']==0
assert sh(N/'verification/logs/coqchk_generic.log')==generic['log_sha256']
assert sh(N/'audit_generic.py')==generic['driver_sha256']
checks['normalized_receipts']={'source_modules_bound':len(receipt['sources']),'successful_steps_bound':len(receipt['checks']),'interface_modules_bound':2,'recursive_source_check':receipt['recursive_source_check'],'compiler':'Coq 8.18.0','independent_compiler_rerun':False,'generic_recursive_check':'recorded exit 0 with matching log'}
# Cross-language path serialization: Lean stores MSB sequence after sentinel;
# Rocq positive decoder peels least significant bits up to sentinel one.
rows=[tuple(map(int,r)) for r in re.findall(r'\((\d+)%positive,(\d+)%positive,(\d+)%N,(\d+)%N\)',(N/'NormalizedCert215.v').read_text())]
shared=read(N/'normalized_certificate.json')['entries'];assert len(rows)==len(shared)==1426
for actual,expected in zip(rows,shared):
    for k in (0,1):assert bin(actual[k])[3:][::-1]==bin(int(expected[k]))[3:]
    assert actual[2:]==tuple(expected[2:]);assert all(0<=j<len(rows) for j in actual[2:])
checks['normalized_data']={'entries':len(rows),'all_paths_and_successors_match_shared_json':True,'data_plus_codec_bytes':(N/'NormalizedCert215.v').stat().st_size+(N/'PathCodec.v').stat().st_size,'json_sha256':sh(N/'normalized_certificate.json')}
# Portable copies of the independently retrieved earlier comparison snapshots.
old=BASE/'comparison_inputs'
comparison_pins=read(old/'SOURCE_PINS.json')
assert len(comparison_pins)==4
assert {row['local_file'] for row in comparison_pins}=={'Prog215.v','DagPerm.v','BisimMirror.v','PathCodec.v'}
for row in comparison_pins:
    data=(old/row['local_file']).read_bytes()
    assert len(data)==row['bytes'] and H(data)==row['sha256'],row['local_file']
    blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    assert blob==row['git_blob_sha'],row['local_file']
comparisons={}
for name in ('Prog215.v','DagPerm.v'):
    comparisons[name]=sh(N/'deps/K215F'/name)==sh(old/name)
for name in ('BisimMirror.v','PathCodec.v'):
    comparisons[name]=sh(N/name)==sh(old/name)
assert all(comparisons.values());checks['prior_source_identity']=comparisons
checks['portable_comparison_inputs']={'files':4,'source_sha256_and_git_blobs_verified':True}
# Lean receipt source and log binding.
D=ROOT/'decoder_lean';drec=read(D/'verification/receipt.json')
for row in drec['modules']:
    assert sh(D/row['source'])==row['source_sha256']
    assert sh(D/'verification/logs'/(row['source']+'.log'))==row['log_sha256']
    assert row['returncode']==0
checks['decoder_receipts']={'source_modules_bound':len(drec['modules']),'compiler':'Lean 4.32.0','independent_compiler_rerun':False,'all_blocks_axioms':'none (recorded)','semantic_axioms':['propext','Classical.choice','Quot.sound']}
# Independent decoding of literal Lean data, not the received generator.
s=(D/'K215Decoder.lean').read_text()
def body(name):return s.split('def '+name+' : ',1)[1].split('#[',1)[1].split('\n]',1)[0]
def bits(text):return [x=='true' for x in re.findall(r'true|false',text)]
def action(text):
    m=re.fullmatch(r'⟨(true|false), (1|\(-1\)), (\d+)⟩',text);assert m,text
    return (int(m[1]=='true'),1 if m[2]=='1' else -1,int(m[3]))
M={}
for q,line in enumerate(body('nativeRows').strip().splitlines()):
    line=line.strip().rstrip(',')
    if line=='none':continue
    acts=re.findall(r'⟨[^⟩]+⟩',line);assert len(acts)==2
    for b,a in enumerate(acts):M[q,b]=action(a)
T={}
for line in (D/'inputs/k215.native.tm').read_text().splitlines():
    if line.startswith('#') or not line.strip():continue
    q,b,w,m,n=line.split();T[int(q),int(b)]=(int(w),1 if m=='R' else -1,int(n))
assert M==T;assert len(M)==430
nodes=[]
for line in body('sourceNodes').strip().splitlines():
    kind,a,b=re.fullmatch(r'\.(leaf|fork) (\d+) (\d+),?',line.strip()).groups();nodes.append((kind,int(a),int(b)))
blocks=[]
for line in body('blocks').strip().splitlines():
    q,r,w,n=re.fullmatch(r'⟨(\d+), (\d+), \[([^]]*)\], (\d+)⟩,?',line.strip()).groups()
    blocks.append((int(q),int(r),bits(w),int(n)))
def replay(block):
    q,r,w,n=block
    if n<=0 or not w:return False
    tape={i+1-len(w):int(b) for i,b in enumerate(w)};start=tape.copy();head=0
    for _ in range(n):
        if head not in tape or (q,tape[head]) not in M:return False
        wr,move,q=M[q,tape[head]];tape[head]=wr;head+=move
    return head==1 and q==r and tape==start
assert len(blocks)==281 and all(map(replay,blocks))
negatives={}
for label,change in [('zero_duration',lambda q,r,w,n:(q,r,w,0)),('wrong_exit',lambda q,r,w,n:(q,999,w,n)),('one_fewer_step',lambda q,r,w,n:(q,r,w,n-1)),('drop_leftmost',lambda q,r,w,n:(q,r,w[1:],n))]:
    negatives[label]=sum(not replay(change(*block)) for block in blocks);assert negatives[label]==281
# Bind all source nodes and expanded source occurrences to packet data.
product=read(D/'inputs/decoder_context_certificate.json');ops={'CI':0,'CD':1,'CB':2,'CC':3,'CH':4}
expected=[('leaf',ops[a],0 if b is None else b) if isinstance(a,str) else ('fork',a,b) for a,b in product['nodes']]
assert nodes==expected
sites=[]
def walk(n,p):
    a,b=product['nodes'][n]
    if isinstance(a,str):sites.append([p,a,b])
    else:walk(a,p+'0');walk(b,p+'1')
walk(product['source_root'],'');assert sites==read(D/'inputs/sites215.json') and len(sites)==4751
# Parse each role and bind to received JSON's exact fields and local block.
roles=[]
for line in body('roles').strip().splitlines():
    mat=re.fullmatch(r'⟨(\d+), (\d+), \[([^]]*)\], \((.*?)\), \((.*?)\)⟩,?',line.strip());assert mat,line
    no,q,w,zero,one=mat.groups();edges=[]
    for e in (zero,one):
        if e.startswith('.internal '):_,r,j=e.split();edges.append(('internal',int(r),int(j)))
        else:
            k,a=e[len('.primitive '):].split(' ',1);edges.append(('primitive',int(k),action(a)))
    roles.append((int(no),int(q),bits(w),edges))
assert len(roles)==234
internal=primitive=0
for i,(node,q,suffix,edges) in enumerate(roles):
    original=product['roles'][i]
    assert [node,q,''.join(str(int(b)) for b in suffix)]==[original['node'],original['state'],original['suffix']]
    assert nodes[node][0]=='fork' and 0<len(suffix)<=2
    for bit,e in enumerate(edges):
        child=nodes[node][bit+1];assert child<node
        oe=original['edges'][bit];assert e[0]==oe['kind']
        if e[0]=='primitive':
            primitive+=1;assert nodes[child][0]=='leaf' and child==e[1]==oe['node'];assert M[q,bit]==e[2]==tuple(oe['action'])
        else:
            internal+=1;r,j=e[1:];assert r==oe['role'];bq,br,bw,bn=blocks[j];rn,rq,rs,_=roles[r]
            word=suffix+[bool(bit)]
            assert rn==child and rs==word[-2:] and bq==q and br==rq and bw==word[-len(bw):] and bn==oe['steps']
assert roles[0][:3]==(201,84,[True]);assert internal==371 and primitive==97
checks['decoder_independent_replay']={'native_rows_bound':len(M),'nodes_bound':len(nodes),'roles_bound':len(roles),'blocks_replayed':len(blocks),'expanded_sites_bound':len(sites),'internal_edges':internal,'primitive_edges':primitive,'negative_controls_rejected':negatives,'scope':'Finite literal data and local traces only; not a theorem or full runtime proof'}
# Zero-credit proof source bound; logs hold five closed reports.
Z=ROOT/'zero_credit';zr=read(Z/'evidence/receipt.json');assert sh(Z/'TagLowering.v')==zr['source_sha256']
assert all(x['exit_code']==0 for x in zr['results']);closed=(Z/'evidence/compile.log').read_text().count('Closed under the global context');assert closed==zr['closed_assumption_reports']==5
checks['zero_credit_receipt']={'source_sha256':zr['source_sha256'],'closed_reports':closed,'recorded_compile_and_recursive_check':'exit 0','independent_compiler_rerun':False}
# Narrow unsafe-proof token scan of concrete .v/.lean files, strip comments.
findings=[]
for p in ROOT.rglob('*'):
    if p.suffix not in ('.v','.lean'):continue
    text=p.read_text();text=re.sub(r'\(\*.*?\*\)|/\-.*?\-/|--[^\n]*','',text,flags=re.S)
    for token in ('sorry','sorryAx','native_decide','Admitted','Axiom'):
        if re.search(r'\b'+token+r'\b',text):findings.append([str(p.relative_to(ROOT)),token])
checks['placeholder_token_scan']=findings
checks['limits']=['No incoming executable run or imported','No Lean/Rocq compiler rerun','No object hash independently reproduced','No full endpoint rebuild or performance baseline','Search214 exhaustive synthesis not rerun']
(BASE/'INDEPENDENT_AUDIT.json').write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps(checks,indent=2))
