import ast,hashlib,json,itertools,random,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];E=D/'research/nine-sharing-sign14-positive74-structural-search/search_canonical.py';G=D/'research/ordinary14-shifted-guard87-probe/candidate.json'
assert hashlib.sha256(E.read_bytes()).hexdigest()=='5f683e6e9b3cc46450e4edcc566610862730b8e58ab574a4e12496dc67b71bb6'
assert hashlib.sha256(G.read_bytes()).hexdigest()=='405dbed5bf465dacac2246e6e8b2c53bcb3dda9b4b13ba277f4a18cdd43ae210'
N=[];I={};names={'node','graph','opof','alternatives','replace'};defs=[n for n in ast.parse(E.read_bytes()).body if isinstance(n,ast.FunctionDef) and n.name in names];assert {n.name for n in defs}==names;exec(compile(ast.Module(body=defs,type_ignores=[]),str(E),'exec'))
assert sys.argv[1:] in ([],['--sphere']);g=json.loads(G.read_text())
if sys.argv[1:]:
 new=[]
 for name,op,a,b in g['source']:
  if name=='Fam':continue
  if name=='Fam2':a=b='Fa'
  if name==g['output']:name='sphere_sum'
  new.append([name,op,a,b])
 new.append([g['output'],'-','sphere_sum',1]);g['source']=new
refs={x:'input:'+x for x in g['witnesses']+g['fixed_numerals']}
for name,op,a,b in g['source']:
 def arg(x):return 'lit:'+str(x) if isinstance(x,int) else refs[x]
 refs[name]=node({'+':'add','-':'sub','*':'mul'}[op],arg(a),arg(b))
root=refs[g['output']];assert len(graph(root))==87
control=node('add',node('mul','control:a','control:b'),node('mul','control:a','control:c'));assert len(graph(control))==3 and min(len(graph(x)) for x in alternatives(control))==2
rng=random.Random(0x8726);beam={root:[]};seen={root};best=(87,root,[])
for depth in range(10):
 candidates={}
 for r,path in beam.items():
  allg=sorted(graph(r));rng.shuffle(allg)
  for target in allg:
   alt=sorted(alternatives(target));rng.shuffle(alt)
   for other in alt:
    nr=replace(r,target,other)
    if nr in seen:continue
    seen.add(nr);count=len(graph(nr))
    if count<best[0]:best=(count,nr,path+[(target,other)]);print('BEST',depth,count,flush=True)
    if count<=89:candidates[nr]=(count,path+[(target,other)])
 if not candidates:break
 ranked=sorted(candidates.items(),key=lambda x:(x[1][0],rng.random()))[:300];beam={r:p for r,(c,p) in ranked};print('DEPTH',depth,'states',len(candidates),'beam',len(beam),'best',best[0],flush=True)
 if best[0]<87:break
print('DONE',best[0],flush=True)
if best[0]<87:print(json.dumps({'root':best[1],'rewrites':best[2],'nodes':N,'original':root,'count':best[0]}))
