from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-fixed-slice-conditional')
for path,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(path).read_bytes()).hexdigest()==h,path
# Exact polynomial certificates, variables b,h,k,tau,ell,q,S,a,x,y,I,V.
N=12;zero=(0,)*N
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
    key=tuple(x+y for x,y in zip(k,j));r[key]=r.get(key,0)+v*w
  return P(r)
 __rmul__=__mul__
 def __eq__(self,o):return self.d==pol(o).d
def pol(x):return x if isinstance(x,P) else P({zero:x})
def var(i):
 e=[0]*N;e[i]=1;return P({tuple(e):1})
b,h,k,tau,ell,q,S,a,x,y,I,V=(var(i) for i in range(N))
B=b*h;r=tau-ell-k+(k*b+1)*h
assert b*(ell+k+r-k*B)-B==b*tau
H=3+4*a;delta=H+a*a;AA=a+2
xn=AA*x+delta*y;yn=x+AA*y
assert xn-a*yn==2*(x-a*y)+H*y
assert AA*AA-delta==1
U=q*q*q*q*q
assert U*(4*q*q*S)==4*q*q*q*q*q*q*q*S
assert y*y-I*I*(y*y-V*V)==(I*V)*(I*V)-(I*I-1)*y*y
# Rank simplification G=(beta-Kprime-1)+(beta-Kprime)*beta.
Kp=h-1; beta=b;qq=b+1
G=(b-Kp-1)+(b-Kp)*b
assert G==qq*(b-Kp)-1
# Source pin sanity; all actual compact constants remain symbolic.
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());rows={r[0]:r[1:] for r in g['source']}
for name,row in {'C':['-','qF','alpha'],'g26':['+','X','K0'],'g27':['*','C','g26'],'Bt':['-','g27','F'],'R':['+','g47','g50'],'Z':['-','g32','Bt'],'A0':['-','g38','g42'],'Dstar':['+','g58','g59'],'A1':['-','g61','g65'],'g72':['-','g71','Q'],'Fa':['-','y2','g82']}.items():assert rows[name]==row
# Small recurrence controls for the main congruence; no huge fixed value.
checks=0
for av in range(1,20):
 hv=3+4*av;dd=hv+av*av;xx,yy=1,0
 for j in range(21):
  assert (xx-av*yy-pow(2,j,hv))%hv==0
  xx,yy=(av+2)*xx+dd*yy,xx+(av+2)*yy
  checks+=1
print(json.dumps({'exact_first_root_identity':True,'exact_main_shift_cancellation':True,'exact_pell_main_congruence_step':True,'exact_strong_auxiliary_norm_rearrangement':True,'exact_rank_factor_identity':True,'small_main_congruence_controls':checks,'fixed_compact_conditions_decided':False,'full_graph_zero_claim':False,'lean_executed':False},sort_keys=True,indent=2))
