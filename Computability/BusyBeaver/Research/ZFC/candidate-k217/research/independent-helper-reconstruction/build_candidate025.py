"""Exact four-row physical reassociation plus contextual69/400 fold.
Own proposal; prefix and blank trace checks only, no primitive certification.
"""
from pathlib import Path
import json,hashlib
import source_language as s,build221 as b
O=Path(__file__).parent;A=Path('/tmp/zfc-intake191/K218_Dominated_Rho8_2026-10-20/K218_Dominated_Rho8_2026-10-20')
old=s.tree(json.loads((A/'source/sites218.json').read_text()));new=s.tree(json.loads((O/'candidate025.sites.json').read_text()));T=b.read_table((A/'binary/machine/k218.native.tm').read_bytes());G,P=b.decoder_map(T,old)
assert s.graph_intervals(s.sites(old))==s.graph_intervals(s.sites(new))==s.graph_arithmetic(s.sites(new))[0]
assert [r[1:]for r in s.sites(old)]==[r[1:]for r in s.sites(new)]
U=T|{(201,0):(0,1,188),(188,0):(0,1,92),(188,1):(1,1,90),(210,0):(0,1,146)}
# Expected association: old92 followed by old90 becomes one41-leaf node.
H=(next(iter(G[92])),next(iter(G[90])))
expected={q:set(ns)for q,ns in G.items()}
# Every proper ancestor keeps its original path/state. The removed80-leaf
# node188 is reused for H at the old in-AX92 path; other nodes remain unchanged.
newnodes=set()
def visit(n):
 newnodes.add(n)
 if not s.leaf(n):visit(n[0]);visit(n[1])
visit(new)
for q,ns in G.items():
 if not ns&newnodes:
  assert len(ns)==len(P[q])==1
  expected[q]={H}if q==188 else{s.subtree(new,P[q][0])}
gg,pp=b.decoder_map(U,new);assert dict(gg)==expected,[(q,len(gg.get(q,set())),len(v))for q,v in expected.items()if gg.get(q,set())!=v]
(O/'candidate025-prefold218.native.tm').write_bytes(b.table_bytes(U))
V={(q,bit):(w,d,69 if z==400 else z)for(q,bit),(w,d,z)in U.items()if q!=400};V[69,0]=(0,-1,188)
expected[69]|=expected.pop(400);vg,vp=b.decoder_map(V,new);assert dict(vg)==expected
# Local read0 route for both guaranteed preceding markers, read1 direct.
local=[]
for marker,target in((0,104),(1,105)):
 tape={-1:marker,0:0};before=tape.copy();q,h=69,0;trace=[]
 for k in range(3):
  assert h in tape;bit=tape[h];w,d,z=V[q,bit];trace.append([q,h,bit,w,d,z]);tape[h]=w;q,h=z,h+d
 assert(q,h,tape)==(target,1,before);local.append({'marker':marker,'target':target,'trace':trace})
assert U[69,1]==U[400,1]==V[69,1]==(1,1,31)
assert sorted((q,bit,w,d)for(q,bit),(w,d,z)in U.items()if z==69)==[(53,1,1,1)]
assert sorted((q,bit,w,d)for(q,bit),(w,d,z)in U.items()if z==400)==[(224,0,0,1)]
# Bound exact blank execution by the accepted parent's recorded complete frame.
parent=json.loads((A/'binary/validation/startup.json').read_text());target=(parent['state'],parent['head'],set(parent['one_cells']))
q,h,ones=0,0,set();count69=0;visited=set()
for ticks in range(400001):
 if(q,h,ones)==target:break
 assert ticks<400000
 bit=int(h in ones);w,d,z=V[q,bit];visited.add((q,bit));count69+=int(q==69 and bit==0)
 if w:ones.add(h)
 else:ones.discard(h)
 q,h=z,h+d
raw=b.table_bytes(V);(O/'candidate025-fold217.native.tm').write_bytes(raw)
result={'status':'OWN_SOURCE_PREFIX_LOCAL_FOLD_AND_BLANK_PASS','source_sha256':hashlib.sha256((O/'candidate025.sites.json').read_bytes()).hexdigest(),'table_sha256':hashlib.sha256(raw).hexdigest(),'working_states':len(V)//2,'source_metrics':s.metrics(new),'changed_prefold_rows':[[q,bit,*a]for(q,bit),a in U.items()if a!=T[q,bit]],'fold':{'keep':69,'drop':400,'helper':188,'local_blocks':local},'blank':{'steps':ticks,'complete_parent_frame_equal':True,'read0_69_visits':count69,'state':q,'head':h,'one_cells':sorted(ones)},'full_decoder_binding':True,'scope':'Exact complete source word/CFG, expected decoder-state/subtree binding, literal local3-step fold with global incoming marker facts, exact bounded blank-frame equality. No full arbitrary-natural primitive runtime check yet.'}
(O/'candidate025-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in('blank','fold')},indent=2));print('blank steps',ticks)
