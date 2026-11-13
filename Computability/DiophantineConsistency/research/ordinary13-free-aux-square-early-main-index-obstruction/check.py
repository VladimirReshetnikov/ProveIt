from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-free-aux-square-early-main-index-obstruction')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-free-aux-square-y3-signed-main-obstruction')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
rec=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
for x in ('xcoord 0 b=1','ycoord 0 b=0','xcoord (time+1) b=','ycoord (time+1) b='):
 assert x in rec,x
assert 'def betaNat : ℕ := 2^(67*8807)-1' in Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
# Exact Pell step for the linear residue, independent of norm assumptions.
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
a,x,y=(var(i) for i in range(3));H=4*a+3;delta=a*a+H
xp=(a+2)*x+delta*y;yp=x+(a+2)*y
assert xp-a*yp==2*(x-a*y)+H*y
assert xp*xp-delta*yp*yp==x*x-delta*y*y
controls=0
for N in range(4,12):
 q=2**N;a=q**3*(q+1);A=a+2;H=4*a+3;x,y=1,0
 for m in range(1,N+1):
  x,y=A*x+(A*A-1)*y,x+A*y
  assert (x-a*y-pow(2,m,H))%H==0
  assert (x*x-(A*A-1)*y*y)==1
  if m<N:
   assert 0<q-2**m<H and 0<q*2**m+1<H
   assert (2**m-q)%H!=0 and (q*2**m+1)%H!=0
   controls+=1
  else:assert (2**m-q)%H==0
print(json.dumps({'prior_y3_obstruction_receipt_reproduced':True,'exact_Pell_step_and_norm_identities':True,'bounded_early_index_controls':controls,'fixed_compact_1_le_m_lt_N_excluded':True,'m_equal_N_positive_sign_left_open':True,'global_graph_zero_or_model_proved':False,'lean_executed':False},sort_keys=True,indent=2))
