from pathlib import Path
from hashlib import sha256
import json,random,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current2011-sheared72-literal-evaluator-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
child=json.loads(Path('research/current2011-sheared72-46-candidate/polynomial.json').read_text())
parent=json.loads(Path('research/current2011-ordinary71-60-candidate/polynomial.json').read_text())
s=(D/'Shear72Literal.lean.src').read_text();body=s.split('def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=',1)[1].split('\nsection Ring',1)[0]
vars=re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.var (\d+)$',body,re.M)
ports=re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.constant \(p (\d+)\)$',body,re.M)
assert vars==[(v,str(i)) for i,v in enumerate(child['witnesses'])]
assert ports==[(v,str(i)) for i,v in enumerate(child['fixed_numerals'])]
rows=[]
for name,a,op,b in re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',body,re.M):
 rows.append([name,op,int(a) if a.isdigit() else a,int(b) if b.isdigit() else b])
assert rows==child['source'] and len(rows)==72 and body.rstrip().endswith('  polynomial')
assert len(re.findall(r'^  let ',body,re.M))==14+4+72
new=[['y_old','+','V','y'],['y_old2','*','y_old','y_old'],['sum_yV','+','y_old','V'],['shear_prod','*','y','sum_yV'],['shear_aux','*','Aaux','shear_prod'],['Na','-','y_old2','shear_aux']]
assert child['source'][:55]==parent['source'][:55] and child['source'][55:61]==new and child['source'][61:]==parent['source'][60:]
assert child['witnesses']==parent['witnesses'] and child['fixed_numerals']==parent['fixed_numerals'] and child['coefficient_binding']==parent['coefficient_binding']
# Exact free-ring identity at the auxiliary cut using sparse integer polynomials.
def add(a,b,k=1):
 z=a.copy()
 for x,n in b.items():z[x]=z.get(x,0)+k*n
 return {x:n for x,n in z.items() if n}
def mul(a,b):
 z={}
 for aa,an in a.items():
  for bb,bn in b.items():
   x=tuple(i+j for i,j in zip(aa,bb));z[x]=z.get(x,0)+an*bn
 return {x:n for x,n in z.items() if n}
V={(1,0,0):1};y={(0,1,0):1};A={(0,0,1):1};old=add(V,y);old2=mul(old,old)
assert add(mul(A,add(mul(V,V),old2,-1)),old2)==add(old2,mul(A,mul(y,add(old,V))),-1)
# Bounded whole-graph diagnostics over signed small integer inputs; not an all-ring proof.
def evaluate(g,p,v):
 env=dict(zip(g['witnesses'],v));env.update(zip(g['fixed_numerals'],p))
 for n,op,a,b in g['source']:
  a=a if isinstance(a,int) else env[a];b=b if isinstance(b,int) else env[b]
  env[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return env
rng=random.Random(7246)
for _ in range(200):
 p=[rng.randint(-2,2) for _ in range(4)];v=[rng.randint(-2,2) for _ in range(14)]
 c=evaluate(child,p,v);vv=v.copy();vv[12]=c['V']+v[12];par=evaluate(parent,p,vv)
 assert c['polynomial']==par['polynomial']
for token in ['theorem eval_expression','theorem value72_eq_sheared71','Function.update v 12','theorem eval_eq_sheared71','OrdinarySphere7160Literal.eval_expression']:
 assert token in s,token
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'literal_row_count':len(rows),'witness_count':len(vars),'port_count':len(ports),'exact_auxiliary_free_ring_identity':True,'signed_whole_graph_controls':200,'lean_executed':False,'graph_file_semantics_formalized':False},sort_keys=True,indent=2))
