import sys
if sys.flags.optimize:
    raise SystemExit("Do not run these evidence checks with -O or PYTHONOPTIMIZE.")
"""Independent sparse-integer verifier, without SymPy or imported generators."""
import ast,hashlib,json,math,random
from pathlib import Path
H=Path(__file__).resolve().parent;ROOT=H.parents[1]
FIX={'Bm1','Kconstant','MC','MF'}
def resolve_parent(relative):
 p=ROOT/relative
 return p if p.is_file() else H/'parents'/Path(relative).name
def norm(p):return {m:c for m,c in p.items() if c}
def add(a,b,k=1):
 d=a.copy()
 for m,c in b.items():d[m]=d.get(m,0)+k*c
 return norm(d)
def mul(a,b):
 d={}
 for m,c in a.items():
  for n,e in b.items():
   z=dict(m)
   for x,j in n:z[x]=z.get(x,0)+j
   t=tuple(sorted(z.items()));d[t]=d.get(t,0)+c*e
 return norm(d)
def const(v):return {():v} if v else {}
def var(v):return {((v,1),):1}
def power(a,n):
 out=const(1)
 for _ in range(n):out=mul(out,a)
 return out
def parse(s,env):
 def rec(n):
  if isinstance(n,ast.Name):return env[n.id]
  if isinstance(n,ast.Constant) and type(n.value)is int:return const(n.value)
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return {m:-c for m,c in rec(n.operand).items()}
  if isinstance(n,ast.BinOp):
   a=rec(n.left)
   if isinstance(n.op,ast.Pow):
    assert isinstance(n.right,ast.Constant) and type(n.right.value)is int and 0<=n.right.value<=8
    return power(a,n.right.value)
   b=rec(n.right)
   if isinstance(n.op,ast.Add):return add(a,b)
   if isinstance(n.op,ast.Sub):return add(a,b,-1)
   if isinstance(n.op,ast.Mult):return mul(a,b)
  raise ValueError(ast.dump(n))
 return rec(ast.parse(s,mode='eval').body)
def degree(p):return max([sum(e for v,e in m if v not in FIX) for m in p]+[0])
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
for file in sorted(H.glob('*_integer_*_degree*.json')):
 p=json.loads(file.read_text())
 parent=json.loads(resolve_parent(p['parent_file']).read_text())
 assert sha(resolve_parent(p['parent_file']))==p['parent_sha256']
 env={v:var(v) for v in set(parent['variables']+p['variables'])|FIX}
 pos={}
 for x,(a,b,c) in p['positivity_parameter_triples'].items():
  pos[x]=add(const(1),add(add(power(var(a),2),power(var(b),2)),mul(var(c),add(var(c),const(1)))))
 actual=[parse(s,env) for s in p['residual_polynomials']]
 if set(parent['variables'])<=set(p['variables']):
  expected=[parse(s,env) for s in parent['residual_polynomials']]+[add(var(x),pos[x],-1) for x in p['positive_ports']]
 else:
  expected=[parse(s,env|pos) for s in parent['residual_polynomials']]
 assert actual==expected,file
 ds=[degree(r) for r in actual]
 assert ds==p['equation_degrees']
 assert len(p['variables'])==p['variable_count'] and len(actual)==p['equation_count']
 assert 2*max(ds)==p['sum_of_squares_exact_degree']
 checks.append({'file':file.name,'exact_residuals':len(actual),'variables':p['variable_count'],'single_polynomial_degree':2*max(ds),'sha256':sha(file)})

# Independently verify each compact circuit namespace, Pos substitution,
# ledger, every factor degree, and exact weighted-degree specialization.
def evalcirc(rows,env,poly=False):
 env=env.copy()
 def atom(x):return (const(x) if poly else x) if isinstance(x,int) else env[x]
 for out,op,a,b in rows:
  a,b=atom(a),atom(b)
  if poly:env[out]=add(a,b) if op=='+' else add(a,b,-1) if op=='-' else mul(a,b)
  else:env[out]=a+b if op=='+' else a-b if op=='-' else a*b
 return env
def weighted_upper_bound(packet,positive_ports):
 # Every cut denotes its exact computed expression, but is thereafter treated
 # as an independent formal symbol carrying a proved degree upper bound.
 # Crucially, a,c,X are cut before the main norm, but Delta=a^2+4a+3 is
 # not: sparse expansion therefore proves its leading cancellation exactly.
 # Similarly the first-root L and auxiliary V cuts precede both occurrences
 # in the shears, so their cancellations are exact, not sampled.
 cuts={'q','wn2','sn2','UM','R10b','first_root_base','R10a','R12','r_lhs',
       'aux_u_rhs','aux_coefficient_root','R16','ordinary_ic2','ordinary_I2',
       'ordinary_Q','ng_D','ng_b','ng_u','norm_first','norm_main','norm_index',
       'norm_transport','norm_strong','norm_aux','ng_unit'}
 weights={x:(2 if x in positive_ports else 1) for x in packet['witnesses']}
 weights.update({x:0 for x in FIX})
 env={x:var(x) for x in weights};bounds={};cut_receipt={}
 def weighted_degree(poly):
  return max([sum(weights[x]*j for x,j in mon) for mon in poly]+[0])
 def atom(x):return const(x) if isinstance(x,int) else env[x]
 for out,op,a,b in packet['source']:
  a,b=atom(a),atom(b)
  poly=add(a,b) if op=='+' else add(a,b,-1) if op=='-' else mul(a,b)
  bounds[out]=weighted_degree(poly)
  if out in cuts:
   x='cut:'+out;weights[x]=bounds[out];env[out]=var(x)
   cut_receipt[out]={'weighted_degree_upper_bound':bounds[out],'exact_sparse_monomials_before_cut':len(poly)}
  else:env[out]=poly
 return bounds[packet.get('output','polynomial')],bounds,cut_receipt
rng=random.Random(0xD10)
for file in sorted(H.glob('start_only_integer*_polynomial*.json')):
 p=json.loads(file.read_text())
 parent=json.loads(resolve_parent(p['source_positive_parent']).read_text())
 assert sha(resolve_parent(p['source_positive_parent']))==p['source_positive_parent_sha256']
 assert p['source'][-len(parent['source']):]==parent['source']
 assert len(p['source'])==p['ledger']['operations']
 assert sum(op=='*' for _,op,_,_ in p['source'])==p['ledger']['M']
 assert len(p['witnesses'])==len(set(p['witnesses']))==p['variable_count']
 known=set(p['witnesses'])|FIX
 for out,op,a,b in p['source']:
  assert out not in known and (isinstance(a,int) or a in known) and (isinstance(b,int) or b in known)
  known.add(out)
 # Every defined variable and witness must be in the output's backward cone.
 used={p['output']}
 for out,op,a,b in reversed(p['source']):
  if out in used:
   used.update(x for x in (a,b) if isinstance(x,str))
 assert set(p['witnesses'])<=used
 assert all(r[0] in used for r in p['source'])
 for _ in range(30):
  e={v:rng.randrange(-3,4) for v in p['witnesses']};e.update({'Bm1':rng.randrange(15,25),'Kconstant':3,'MC':2,'MF':20})
  before=e.copy()
  for x in p['positive_ports']:
   a,b,c=(e[x+'_pos_'+u] for u in 'abc');before[x]=1+a*a+b*b+c*(c+1)
  assert evalcirc(p['source'],e)['polynomial']==evalcirc(parent['source'],before)['polynomial']
 env={v:mul(const(j+2),var('t')) for j,v in enumerate(p['witnesses'])}
 env.update({'Bm1':const(15),'Kconstant':const(3),'MC':const(2),'MF':const(19)})
 result=evalcirc(p['source'],env,True)
 assert degree(result['polynomial'])==p['exact_degree']
 upper,gatebounds,cutreceipt=weighted_upper_bound(parent,p['positive_ports'])
 assert upper==p['exact_degree']
 fdegrees=[degree(result[f]) for f in p.get('factor_names',[])]
 if fdegrees:assert fdegrees==p['factor_exact_degrees']
 checks.append({'file':file.name,'namespace_liveness_and_ledger':'PASS','random_exact_substitutions':30,
                'specialization_degree':p['exact_degree'],'proved_weighted_degree_upper_bound':upper,
                'exact_cut_receipt':cutreceipt,'factor_degrees':fdegrees,'sha256':sha(file)})
# Finite corroboration only: theorem is proved separately.
values={1+a*a+b*b+c*(c+1) for a in range(33) for b in range(33) for c in range(33)}
assert all(n in values for n in range(1,1001))
receipt={'status':'PASS','method':'Independent sparse integer arithmetic and AST parsing. No SymPy and no imported source or emitter programs.','checks':checks,'positive_representation_first_1000':'PASS','scope':'Checks literal substitutions and exact degrees; the signed-domain and compiler proofs remain mathematical obligations.'}
(H/'INDEPENDENT_INTEGER_AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
