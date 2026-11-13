from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary10-carrier60-all-ports-second-independent')
for path,digest in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(path).read_bytes()).hexdigest()==digest,path
P=Path('research/ordinary10-carrier60-universal-zero-independent')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P/'check.py')])==(P/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary10-carrier60-inverse-boundary/candidate.json').read_text())
expected=['n_J','n_F','n_C','n_w','n_s','n_h','n_tau','n_eta','n_zeta','n_gamma']
assert g['witnesses']==expected and g['fixed_numerals']==['beta','K0','MC','MF'] and len(g['source'])==60
z=(0,0,0,0)
def const(n):return {z:n} if n else {}
def var(i):
 t=[0,0,0,0];t[i]=1;return {tuple(t):1}
def add(a,b,sign=1):
 out=a.copy()
 for e,v in b.items():out[e]=out.get(e,0)+sign*v
 return {e:v for e,v in out.items() if v}
def mul(a,b):
 out={}
 for e,v in a.items():
  for f,w in b.items():
   k=tuple(x+y for x,y in zip(e,f));out[k]=out.get(k,0)+v*w
 return {k:v for k,v in out.items() if v}
d={name:var(i) for i,name in enumerate(g['fixed_numerals'])}
vals=[0,d['K0'],0,1,0,0,3363,1527,850,292]
for name,value in zip(expected,vals):d[name]=const(value) if isinstance(value,int) else value
order=set(d)
for n,op,x,y in g['source']:
 assert n not in order and op in ('+','-','*')
 assert isinstance(x,int) or x in order
 assert isinstance(y,int) or y in order
 x=const(x) if isinstance(x,int) else d[x];y=const(y) if isinstance(y,int) else d[y]
 d[n]=add(x,y) if op=='+' else add(x,y,-1) if op=='-' else mul(x,y)
 order.add(n)
for key,value in {'qm':0,'q':1,'X':1,'Y':1,'U':1,'C':1,'R':0,'a':2,'H':11,'Delta':15,'k':2378,'c':3905,'ell':2378,'Dstar':-15124,'Bres':0,'firstres':0,'A1':0,'out':0}.items():assert d[key]==const(value),key
assert d['F']==add(var(1),const(1)) and d['qF']==mul(const(-1),var(1))
assert 3363**2==1+2*2378**2 and 15124**2==1+15*3905**2
alpha=add(d['qF'],d['C'],-1);assert alpha==add(mul(const(-1),var(1)),const(-1))
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'author_receipt_reproduced':True,'literal_rows_evaluated':len(g['source']),'inputs_in_declared_order':True,'universal_output_is_zero_polynomial':d['out']=={},'signed_main_root':-15124,'reconstructed_alpha':'-K0-1','source_domain':'four nonnegative integer ports','existential_equivalence_to_61_or_parent_proved':False,'lean_executed':False},sort_keys=True,indent=2))
