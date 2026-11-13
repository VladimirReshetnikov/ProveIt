from pathlib import Path
from hashlib import sha256
import ast,itertools,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary9-two-norm64-rewrite-search')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/nine-sharing-sign14-positive74-structural-search/search_canonical.py');G=Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json')
N=[];I={};wanted={'node','graph','opof','alternatives','replace'}
defs=[n for n in ast.parse(P.read_bytes()).body if isinstance(n,ast.FunctionDef) and n.name in wanted]
assert {n.name for n in defs}==wanted;exec(compile(ast.Module(body=defs,type_ignores=[]),str(P),'exec'))
g=json.loads(G.read_text());refs={x:'input:'+x for x in g['witnesses']+g['fixed_numerals']}
for name,op,a,b in g['source']:
 def arg(x):return 'lit:'+str(x) if isinstance(x,int) else refs[x]
 refs[name]=node({'+':'add','-':'sub','*':'mul'}[op],arg(a),arg(b))
root=refs[g['output']];count=len(graph(root));assert count==64
control=node('add',node('mul','control:a','control:b'),node('mul','control:a','control:c'))
assert len(graph(control))==3 and min(len(graph(x)) for x in alternatives(control))==2
rng=random.Random(906414);beam={root:[]};seen={root};best=(64,root,[]);depths=[]
for depth in range(8):
 candidates={}
 for r,path in beam.items():
  allg=sorted(graph(r));rng.shuffle(allg)
  for target in allg:
   alts=sorted(alternatives(target));rng.shuffle(alts)
   for other in alts:
    nr=replace(r,target,other)
    if nr in seen:continue
    seen.add(nr);c=len(graph(nr))
    if c<best[0]:best=(c,nr,path+[(target,other)])
    if c<=65:candidates[nr]=(c,path+[(target,other)])
 if not candidates:break
 ranked=sorted(candidates.items(),key=lambda x:(x[1][0],rng.random()))[:100]
 beam={r:p for r,(c,p) in ranked};depths.append({'depth':depth,'candidates':len(candidates),'retained':len(beam),'best':best[0]})
 if best[0]<64:break
out={'candidate_sha256':sha256(G.read_bytes()).hexdigest(),'initial_live_operations':count,
 'factor_control':True,'beam_width':100,'max_depth':8,'max_gates_kept':65,'seed':906414,
 'depths':depths,'best_live_operations':best[0],'nodes_generated':len(N),
 'scope':'Bounded exact-ring local rewrites; no compact-specialized, zero-set, provider or Lean claim.'}
if best[0]<64:out.update({'rewrites':best[2],'root':best[1],'nodes':N})
print(json.dumps(out,sort_keys=True,indent=2))
