"""Independent literal modular replay. Only Python standard library; no builder import."""
import ast,gzip,hashlib,json,random
from pathlib import Path
R=Path(__file__).resolve().parent

def req(b,m):
 if not b:raise ValueError(m)
def ev(s,e,p):
 def rec(n):
  if isinstance(n,ast.Constant):req(isinstance(n.value,int),'integer literal');return n.value%p
  if isinstance(n,ast.Name):return e[n.id]%p
  if isinstance(n,ast.UnaryOp):req(isinstance(n.op,ast.USub),'unary');return -rec(n.operand)%p
  req(isinstance(n,ast.BinOp),'syntax')
  a=rec(n.left)
  if isinstance(n.op,ast.Pow):req(isinstance(n.right,ast.Constant) and 0<=n.right.value<=100,'power');return pow(a,n.right.value,p)
  b=rec(n.right)
  if isinstance(n.op,ast.Add):return (a+b)%p
  if isinstance(n.op,ast.Sub):return (a-b)%p
  if isinstance(n.op,ast.Mult):return a*b%p
  raise ValueError('operator')
 return rec(ast.parse(s,mode='eval').body)
binding=json.loads((R/'BINDING.json').read_text());fixed={}
for n,d in binding['ports'].items():
 rawgz=(R/d['path']).read_bytes();raw=gzip.decompress(rawgz)
 req(hashlib.sha256(rawgz).hexdigest()==d['gzip_sha256'],n+' gzip hash')
 req(hashlib.sha256(raw).hexdigest()==d['raw_sha256'],n+' raw hash')
 fixed[n]=int.from_bytes(raw,'little');req(fixed[n].bit_length()==d['bits'],n+' bits')
req(fixed['beta']==(1<<1064921)-1,'beta');req(fixed['cone_A']==1<<1113,'A');req(fixed['cone_B']==1<<666104,'B')
src=json.loads((R/'inherited/degree12_24.json').read_text());rng=random.Random(20261024);count=0
for path in sorted(R.glob('integer*.json')):
 d=json.loads(path.read_text());req(len(d['variables'])==d['variable_count'],'count');req(len(d['variables'])==len(set(d['variables'])),'unique');req(len(d['residuals'])==d['equation_count'],'row count')
 names={n.id for x in d['residuals'] for n in ast.walk(ast.parse(x,mode='eval')) if isinstance(n,ast.Name)}
 req(names==set(d['variables']+d['fixed_numerals']),'liveness '+path.name)
 for p in [65521,1000003,1000033]:
  for _ in range(50):
   e={n:rng.randrange(-2*p,2*p) for n in d['variables']};e.update({n:x%p for n,x in fixed.items()})
   old=dict(e)
   # Every emitted restoration is fully inlined in the surviving coordinates.
   old.update({n:ev(x,e,p) for n,x in d['restoration'].items()})
   old['tau']=(e['tau']+old['E']*(old['c']-old['eta']))%p
   if d['auxiliary_root_shear']:old['y']=(e['f']*e['o']+e['y'])%p
   oldrows=[ev(x,old,p) for x in src['residuals']]
   if d['auxiliary_root_shear']:
    correction=oldrows[9]*(old['y']**2-old['V']**2)
    oldrows[10]=(oldrows[10]+correction)%p
   for i in d['deleted_source_rows']:req(oldrows[i]==0,path.name+' deleted '+str(i))
   expected=[v for i,v in enumerate(oldrows) if i not in d['deleted_source_rows']]
   actual=[ev(x,e,p) for x in d['residuals']]
   req(actual==expected,path.name+' restored rows')
   count+=1
print(json.dumps({'status':'pass','literal_signed_modular_replays':count,'packets':5,'fixed_payloads':len(fixed),'unbounded_correctness':'mathematical proof, not established by finite replay'},indent=2))
