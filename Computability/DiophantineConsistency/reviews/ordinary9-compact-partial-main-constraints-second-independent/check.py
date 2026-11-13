from pathlib import Path
from hashlib import sha256
from math import gcd,isqrt
import ast,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary9-compact-partial-main-constraints-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for n in ('ordinary9-shifted-two-norm-compact-first-compatible-partial','ordinary9-compact-partial-main-index-constraints'):
 p=Path('research')/n;assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
# Exact carrier identity as a polynomial in t,Kprime,rho^42.
N=3;zero=(0,0,0)
def C(v):return {zero:v} if v else {}
def V(i):
 e=[0,0,0];e[i]=1;return {tuple(e):1}
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
t,kp,P=[V(i) for i in range(3)];one=C(1);two=C(2);beta=add(mul(two,t),one);q=add(beta,one);w=sub(t,kp);K0=add(mul(beta,P),kp);X=mul(q,w);C0=sub(beta,two)
h=add(mul(C0,add(w,P)),sub(t,one));B=sub(mul(C0,add(X,K0)),one)
assert B==mul(beta,h)
# Independently reconstruct source kernel residues using coefficient Horner.
root=Path('Lean/DiophantineConsistency/Compact44');txt=(root/'Compact943Data.lean').read_text();body=txt.split('-- BEGIN PINNED ORDERED ROWS')[1].split('-- END PINNED ORDERED ROWS')[0]
rows=ast.literal_eval('['+body+']');slots=ast.literal_eval(re.search(r'^def slots : List ℕ := (\[[^\n]+\])$',(root/'CompactSymbolicKernel.lean').read_text(),re.M).group(1))
assert len(rows)==943 and len(slots)==41
coef=[0]*5496
for e in (30,62,1100,2201,42):coef[e]+=1
for j,(a,b,c,d) in enumerate(rows):
 val=a+2**8*b+2**17*c+2**25*d+127*2**34;assert 0<val<2**41
 sel=1+2**10*(2**41-val);coef[4393-j]+=sel;coef[5495-j]+=sel
for j,p in enumerate(slots):coef[4393-p]+=2**(10+j);coef[5495-p]+=2**(10+j)
def isprime(p):return p>=2 and all(p%i for i in range(2,isqrt(p)+1))
def discrete_log(base,target,p,order):
 # Baby-step giant-step, different from the author's full cycle listing.
 step=isqrt(order)+1;baby={};x=1
 for j in range(step):baby.setdefault(x,j);x=x*base%p
 factor=pow(pow(base,step,p),-1,p);y=target%p
 for i in range(step+1):
  if y in baby:
   k=i*step+baby[y]
   if k<order and pow(base,k,p)==target%p:return k
  y=y*factor%p
 raise AssertionError((base,target,p,order))
results=[]
for p,order,fac in ((16267,5422,(2,2711)),(16979,16978,(2,13,653))):
 assert isprime(p) and pow(2,order,p)==1 and all(pow(2,order//x,p)!=1 for x in fac)
 rho=pow(2,67,p);kp=0
 for v in reversed(coef):kp=(kp*rho+v)%p
 q=pow(2,67*8807,p);w=((q-2)*pow(2,-1,p)-kp)%p;X=q*w%p
 H=(4*pow(q,3,p)*(X+1)+3)%p;assert H==0 and X!=0
 results.append([p,q,kp,w,X,order,discrete_log(2,X,p,order),discrete_log(2,-pow(X,-1,p)%p,p,order)])
assert results==[[16267,2086,6569,10740,3981,5422,553,2158],[16979,16434,1864,6352,1876,16978,10155,15312]]
def crt(a,m,b,n):
 g=gcd(m,n);assert (b-a)%g==0
 modulus=m*(n//g);t=((b-a)//g*pow(m//g,-1,n//g))%(n//g)
 return (a+m*t)%modulus,modulus
assert crt(553,5422,10155,16978)==(31198741,46027358)
assert crt(2158,5422,15312,16978)==(37842296,46027358)
# Independent finite interval/uniqueness controls.
controls=0
for X0 in range(1,6):
 for Y in range(8,15):
  M=X0*Y*Y;A=Y*(X0+1)+2;Af=2*M+1;B=2*A-1
  assert 2*A<Af and B>2*(Y+1) and B*B>2*Af
  tau,k=1,0
  for n in range(1,7):
   tau,k=Af*tau+2*M*(M+1)*k,2*tau+Af*k
   x,y=1,0;hits=[]
   for m in range(1,2*n+4):
    x,y=A*x+(A*A-1)*y,x+A*y
    if Y*k<=y<(Y+1)*k:hits.append(m)
   assert len(hits)<=1 and all(n<m<2*n for m in hits);controls+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'both_author_receipts_reproduced':True,'carrier_exact_polynomial_identity':True,
 'independent_kernel_Horner_and_BSGS':results,'generalized_CRT_sign_classes':True,
 'interval_uniqueness_controls':controls,'main_norm_solved':False,
 'original_parent_bridge_proved':False,'lean_executed':False},sort_keys=True,indent=2))
