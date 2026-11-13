from pathlib import Path
from hashlib import sha256
from math import isqrt
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-eta85-main-ordinate-q-bound-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-eta85-main-ordinate-q-bound');assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
# Confirm all three cited graphs, including the alpha probe, retain the
# exact shifted-k and main residual circuit.
paths=['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json','research/ordinary13-eta85-shift-boundary-probes/F-probe.json','research/ordinary13-eta85-shift-boundary-probes/alpha-probe.json']
for path in paths:
 g=json.loads(Path(path).read_text());r={row[0]:row[1:] for row in g['source']}
 for n,row in {'s':['+','n_s',1],'q':['+',1,'qm'],'X':['*','q','n_w'],'q2':['*','q','q'],'q3':['*','q','q2'],'Y':['*','q3','s'],'U':['*','Y','q2'],'kbase':['+','n_eta','n_zeta'],'k':['+','kbase',1],'kY':['*','Y','k'],'c':['+','n_eta','kY'],'a':['+','E','Y'],'H':['+',3,'g15'],'Delta':['+','H','g17'],'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],'g63':['*','Delta','c2'],'g64':['+',1,'g63'],'g65':['*','g62','g64'],'A1':['-','g61','g65']}.items():assert r[n]==row,(path,n,r.get(n))
# Independently check exact algebraic forms in Z[A,c,d].
Z=(0,0,0)
class P:
 def __init__(self,d):self.d={k:v for k,v in d.items() if v}
 def __add__(self,o):
  o=pol(o);r=self.d.copy()
  for k,v in o.d.items():r[k]=r.get(k,0)+v
  return P(r)
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.d.items()})
 def __sub__(self,o):return self+-pol(o)
 def __rsub__(self,o):return pol(o)+-self
 def __mul__(self,o):
  o=pol(o);r={}
  for k,v in self.d.items():
   for j,w in o.d.items():
    key=tuple(a+b for a,b in zip(k,j));r[key]=r.get(key,0)+v*w
  return P(r)
 __rmul__=__mul__
 def __eq__(self,o):return self.d==pol(o).d
def pol(x):return x if isinstance(x,P) else P({Z:x})
def var(i):
 e=[0]*3;e[i]=1;return P({tuple(e):1})
A,c,d=(var(i) for i in range(3));delta=A*A-1;t=A*c-d;dp=A*d-delta*c
assert dp+A*t==c and dp*dp-delta*t*t==d*d-delta*c*c
rad=1+delta*c*c
assert rad-(A*c-1)*(A*c-1)==c*(2*A-c)
assert rad-(A-1)*c*(A-1)*c==1+2*(A-1)*c*c
# Direct enumeration of full interval; c=2A is the only solution after c=1.
controls=solutions=0
for A0 in range(2,81):
 for c0 in range(2,2*A0*A0):
  rad0=1+(A0*A0-1)*c0*c0;d0=isqrt(rad0);controls+=1
  if d0*d0==rad0:assert c0==2*A0;solutions+=1
assert solutions==79
print(json.dumps({'author_receipt_reproduced':True,'three_cited_graphs_shifted_k_and_main_circuit_checked':True,'inverse_and_square_gap_polynomial_identities':True,'bounded_interval_controls':controls,'bounded_nontrivial_solutions':solutions,'standard_integer_argument_scope_only':True,'main_residual_extraction_or_model_proved':False,'lean_executed':False},sort_keys=True,indent=2))
