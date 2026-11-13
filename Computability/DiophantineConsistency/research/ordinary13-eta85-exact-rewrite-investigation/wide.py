import ast,hashlib,json,itertools,random,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path('research/nine-sharing-sign14-positive74-structural-search/search_canonical.py')
assert hashlib.sha256(P.read_bytes()).hexdigest()=='5f683e6e9b3cc46450e4edcc566610862730b8e58ab574a4e12496dc67b71bb6'
G=Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json')
assert hashlib.sha256(G.read_bytes()).hexdigest()=='97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648'
N=[];I={};wanted={'node','graph','opof','alternatives','replace'}
defs=[n for n in ast.parse(P.read_bytes()).body if isinstance(n,ast.FunctionDef) and n.name in wanted]
assert {n.name for n in defs}==wanted
exec(compile(ast.Module(body=defs,type_ignores=[]),str(P),'exec'))
g=json.loads(G.read_text());refs={x:'input:'+x for x in g['witnesses']+g['fixed_numerals']}
for name,op,a,b in g['source']:
 def arg(x):return 'lit:'+str(x) if isinstance(x,int) else refs[x]
 refs[name]=node({'+':'add','-':'sub','*':'mul'}[op],arg(a),arg(b))
root=refs[g['output']];count=len(graph(root));assert count==85
control=node('add',node('mul','control:a','control:b'),node('mul','control:a','control:c'))
assert len(graph(control))==3 and min(len(graph(x)) for x in alternatives(control))==2
rng=random.Random(851311);beam={root:[]};seen={root};best=(85,root,[]);depths=[]
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
    if c<=86:candidates[nr]=(c,path+[(target,other)])
 if not candidates:break
 ranked=sorted(candidates.items(),key=lambda x:(x[1][0],rng.random()))[:120]
 beam={r:p for r,(c,p) in ranked};depths.append({'depth':depth,'candidates':len(candidates),'retained':len(beam),'best':best[0]})
 if best[0]<85:break
out={'parent_sha256':hashlib.sha256(G.read_bytes()).hexdigest(),'initial_live_operations':count,
 'factor_control':True,'beam_width':120,'max_depth':8,'max_gates_kept':86,'seed':851311,
 'depths':depths,'best_live_operations':best[0],'nodes_generated':len(N),
 'scope':'Bounded exact-ring structural rewrites; not exhaustive or a Lean theorem.'}
if best[0]<85:out.update({'rewrites':best[2],'root':best[1],'nodes':N})
print(json.dumps(out,sort_keys=True,indent=2))
