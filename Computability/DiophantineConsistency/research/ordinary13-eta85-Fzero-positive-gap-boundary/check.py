from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta85-Fzero-positive-gap-boundary')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-eta85-shift-boundary-probes')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads((p/'F-probe.json').read_text());rows={n:(op,a,b) for n,op,a,b in g['source']}
for n,row in {'qm':('*','n_J','beta'),'q':('+',1,'qm'),'X':('*','q','n_w'),
 'Y':('*','q3','s'),'kbase':('+','n_eta','n_zeta'),'k':('+','kbase',1),
 'kY':('*','Y','k'),'c':('+','n_eta','kY'),'a':('+','E','Y'),
 'C':('-','qF','alpha'),'Bt':('-','g27','n_F'),'Z':('-','g32','Bt'),
 'A0':('-','g38','g42'),'A1':('-','g61','g65')}.items():assert rows[n]==row,(n,rows[n])
assert len(g['source'])==84 and g['witnesses'][1]=='n_F'
# Independent exact polynomial identities for the square gap.
N=2;z=(0,0)
def var(i):e=[0,0];e[i]=1;return {tuple(e):1}
def C(v):return {z:v} if v else {}
def add(a,b,k=1):
 d=a.copy()
 for e,v in b.items():d[e]=d.get(e,0)+k*v
 return {e:v for e,v in d.items() if v}
def sub(a,b):return add(a,b,-1)
def mul(a,b):
 d={}
 for e,v in a.items():
  for f,w in b.items():
   t=tuple(x+y for x,y in zip(e,f));d[t]=d.get(t,0)+v*w
 return {e:v for e,v in d.items() if v}
A,c=var(0),var(1);one=C(1);two=C(2);Ac=mul(A,c)
rad=add(one,mul(sub(mul(A,A),one),mul(c,c)))
assert sub(rad,mul(sub(Ac,one),sub(Ac,one)))==mul(c,sub(mul(two,A),c))
assert sub(mul(Ac,Ac),rad)==sub(mul(c,c),one)
# Compact-like positive natural ports exhibit A0=0 with F=0,C>0,
# k=2; no claim is made that their main residual vanishes.
count=0
for beta in range(1,10):
 for K in range(1,8):
  r=(2*beta+1)*K-1;v=[1,0,0,1,0,0,0,0,r,0,1,1,0];ports=[beta,K,0,0]
  d=dict(zip(g['witnesses'],v));d.update(zip(g['fixed_numerals'],ports))
  for n,op,x,y in g['source']:
   x=d[x] if isinstance(x,str) else x;y=d[y] if isinstance(y,str) else y
   d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
  assert d['C']==beta and d['k']==2 and d['Z']==beta and d['A0']==0
  assert d['Y']>1 and d['c']==2*d['Y'] and d['c']<2*(d['a']+2)
  assert d['A1']!=0
  count+=1
# Finite controls for every k=1,2 and eta<k (all q>=2, s>=1, X>=0).
for q in range(2,9):
 for s in range(1,5):
  Y=q**3*s
  for X in range(8):
   a=X*Y+Y;A=a+2
   for k in (1,2):
    for eta in range(k):
     c=Y*k+eta
     assert 1<c<2*A and (A*c-1)**2<1+(A*A-1)*c*c<(A*c)**2
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'exact_square_gap_polynomial_identities':True,'actual_Fzero_first_norm_controls':count,
 'k_one_two_main_gap_controls':True,'compact_zero_or_reverse_map_proved':False,
 'lean_executed':False},sort_keys=True,indent=2))
