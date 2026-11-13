from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta85-main-small-k-gap-four')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-eta85-Fzero-positive-gap-boundary')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text());rows={n:(op,a,b) for n,op,a,b in g['source']}
for n,row in {'kbase':('+','n_eta','n_zeta'),'k':('+','kbase',1),'c':('+','n_eta','kY'),
 'a':('+','E','Y'),'Delta':('+','H','g17'),'A1':('-','g61','g65')}.items():assert rows[n]==row
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
A,c=var(0),var(1);one=C(1);two=C(2);three=C(3);four=C(4);Ac=mul(A,c)
rad=add(one,mul(sub(mul(A,A),one),mul(c,c)))
assert sub(rad,mul(sub(Ac,two),sub(Ac,two)))==sub(mul(c,sub(mul(four,A),c)),three)
assert sub(mul(sub(Ac,one),sub(Ac,one)),rad)==mul(c,sub(c,mul(two,A)))
controls=0
for q in range(2,9):
 for s in range(1,5):
  Y=q**3*s
  for X in range(8):
   a=Y*(X+1);A=a+2
   for k in (3,4):
    for eta in range(k):
     c=Y*k+eta;rad=1+(A*A-1)*c*c
     if X>=1:assert 1<c<2*A and (A*c-1)**2<rad<(A*c)**2
     else:assert 2*A<c<4*A and (A*c-2)**2<rad<(A*c-1)**2
     controls+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'prior_small_gap_receipt_reproduced':True,'exact_second_gap_polynomials':True,
 'natural_small_k_controls':controls,'external_main_norm_implies_k_at_least_five':True,
 'lean_executed':False},sort_keys=True,indent=2))
