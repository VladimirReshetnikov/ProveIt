from pathlib import Path
from hashlib import sha256
from math import isqrt
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta85-main-ordinate-q-bound')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-eta85-main-small-k-gap-four')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
for name in ('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json','research/ordinary13-eta85-shift-boundary-probes/F-probe.json'):
 g=json.loads(Path(name).read_text());r={n:(op,a,b) for n,op,a,b in g['source']}
 for n,row in {'q':('+',1,'qm'),'X':('*','q','n_w'),'Y':('*','q3','s'),
  'kbase':('+','n_eta','n_zeta'),'k':('+','kbase',1),'c':('+','n_eta','kY'),
  'a':('+','E','Y'),'H':('+',3,'g15'),'Delta':('+','H','g17'),
  'A1':('-','g61','g65')}.items():assert r[n]==row,(name,n,r[n])
# Exact ring identities for the Pell inverse pair, without assuming its norm.
N=3;zero=(0,)*N
def C(v):return {zero:v} if v else {}
def var(i):
 a=[0]*N;a[i]=1;return {tuple(a):1}
def add(a,b,sgn=1):
 r=a.copy()
 for k,v in b.items():r[k]=r.get(k,0)+sgn*v
 return {k:v for k,v in r.items() if v}
def sub(a,b):return add(a,b,-1)
def mul(a,b):
 r={}
 for e,v in a.items():
  for f,w in b.items():
   k=tuple(x+y for x,y in zip(e,f));r[k]=r.get(k,0)+v*w
 return {k:v for k,v in r.items() if v}
A,c,d=[var(i) for i in range(3)];one=C(1)
delta=sub(mul(A,A),one);t=sub(mul(A,c),d);dp=sub(mul(A,d),mul(delta,c))
assert add(dp,mul(A,t))==c
assert sub(mul(dp,dp),mul(delta,mul(t,t)))==sub(mul(d,d),mul(delta,mul(c,c)))
# Under d²=1+delta*c², positivity comparator (A*d)²−(delta*c)².
assert sub(mul(mul(A,A),add(one,mul(delta,mul(c,c)))),mul(delta,mul(delta,mul(c,c))))==add(mul(A,A),mul(delta,mul(c,c)))
# Direct finite controls for all 1<=k<=q and the required shift constraint.
controls=0
for q in range(2,15):
 for s in range(1,4):
  Y=q**3*s
  for w in range(4):
   X=q*w;a=Y*(X+1);A=a+2
   for k in range(1,q+1):
    for eta in range(k):
     c=Y*k+eta;rad=1+(A*A-1)*c*c
     assert isqrt(rad)**2!=rad
     if w>0:assert 1<c<2*A
     else:
      assert 1<c<2*A*A
      assert c<2*A if k<=2 else c>2*A
     controls+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'actual_parent_and_F_probe_main_rows':True,'Pell_inverse_polynomial_identities':True,
 'finite_q_bound_controls':controls,'main_norm_implies_k_greater_than_q_over_standard_integers':True,
 'lean_executed':False,'model_or_zero_extraction_proved':False},sort_keys=True,indent=2))
