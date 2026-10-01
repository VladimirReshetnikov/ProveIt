"""Independent exact rational-exponent checks; standard library only."""
from fractions import Fraction as F
from math import factorial, comb
from pathlib import Path
import json
BASE=Path(__file__).resolve().parent

def trim(p):
 p=list(p)
 while len(p)>1 and not p[-1]:p.pop()
 return p

def add(*args):
 z=[0]*max(map(len,args))
 for p in args:
  for i,x in enumerate(p):z[i]+=x
 return trim(z)
def scale(p,c):return trim([c*x for x in p])
def mul(p,q):
 z=[0]*(len(p)+len(q)-1)
 for i,x in enumerate(p):
  for j,y in enumerate(q):z[i+j]+=x*y
 return trim(z)
def power(p,n):
 z=[1]
 for _ in range(n):z=mul(z,p)
 return z
def ev(p,x):
 v=0
 for c in reversed(p):v=v*x+c
 return v

def check(test,label):
 if not test:raise RuntimeError(label)

cert=json.loads((BASE/'certificates.json').read_text())
den=[1,2]; bn=[-1,-1,-1,-2]; en=[0,1,1]
quartics=[]
for rec in cert['quartic_certificates']:
 r=rec['r'];prime=rec['prime']
 fn=scale(mul(en,[-1,r+1]),-2)
 A=scale(power(den,2),150 if r==4 else 10)
 B=scale(mul(bn,den),30 if r==4 else 10)
 C=scale(mul(en,den),-10)
 D=add(power(bn,2),scale(mul(fn,den),-10))
 # Closed discriminant for A*K^4+B*K^2+C*K+D, no resultant routine.
 disc=add(scale(mul(power(A,3),power(D,3)),256),
          scale(mul(mul(power(A,2),power(B,2)),power(D,2)),-128),
          scale(mul(mul(mul(power(A,2),B),power(C,2)),D),144),
          scale(mul(power(A,2),power(C,4)),-27),
          scale(mul(mul(A,power(B,4)),D),16),
          scale(mul(mul(A,power(B,3)),power(C,2)),-4))
 DD=list(reversed(rec['D_coefficients_descending']))
 expected=scale(mul(power(den,6),DD),rec['discriminant_constant'])
 check(disc==expected,('discriminant',r))
 values=[ev(DD,j)%prime for j in range(prime)]
 check(values==rec['D_values_mod_prime'] and all(values),('values',r))
 check(DD[-1]%prime==rec['leading_coefficient_mod_prime']!=0,('leading',r))
 # Polynomial remainder modulo a^prime-a.
 rem=[v%prime for v in DD]
 for j in range(len(rem)-1,prime-1,-1):
  rem[j-prime+1]=(rem[j-prime+1]+rem[j])%prime
  rem[j]=0
 rem=trim(rem)
 displayed=[2] if r==4 else [-5,4,2,4,-4,5,5,3,3,-1,-2]
 check(rem==trim([v%prime for v in displayed]),('displayed remainder',r))
 quartics.append({'r':r,'closed_formula_discriminant_pass':True,'values_mod_prime':values,'remainder_ascending':rem})

# Fresh exact differentiation recurrence, compared to direct A/B powers.
MAXR=6; MAXN=28
params=[F(1,3),F(1,2),F(2,3),F(3,4),F(4,5),F(3,2),F(2),F(5,2)]
def conv(p,q):
 v=[F(0)]*(MAXR+1)
 for i,x in enumerate(p):
  for j,y in enumerate(q):
   if i+j<=MAXR:v[i+j]+=x*y
 return v
checks=0;centerchecks=0;reflectionchecks=0
for a in params:
 # Generalized binomial coefficients independently from falling products.
 choose=[F(1)]
 for j in range(1,MAXR+2):choose.append(choose[-1]*(a-j+1)/j)
 A=[sum(choose[j]*F((-1)**(n-j),n-j+1) for j in range(n+1)) for n in range(MAXR+1)]
 B=[choose[n+1]/a for n in range(MAXR+1)]
 AP=[[F(1)]+[F(0)]*MAXR];BP=[AP[0]]
 for j in range(MAXN):AP.append(conv(AP[-1],A));BP.append(conv(BP[-1],B))
 coeff={(0,0):F(1)}
 for N in range(1,MAXN+1):
  prev=coeff;coeff={}
  for (ell,k),v in prev.items():
   for key,val in [((ell,k),(a*ell-(N-1))*v),((ell,k-1),k*v),((ell+1,k),v),((ell+1,k+1),a*v)]:
    if key[1]>=0:coeff[key]=coeff.get(key,F(0))+val
  for r in range(min(MAXR,N-1)+1):
   ell=N-r
   for k in range(ell+1):
    residual=conv(AP[ell-k],BP[k])[r]
    pred=a**k*F(factorial(N),factorial(ell))*comb(ell,k)*residual
    check(pred==coeff.get((ell,k),0),('Bell',a,N,r,k))
    checks+=1
    K=a*k-(2*a-1)*N+2*a*r-1
    U=a*a*k-N-1;V=N+1-a**4*k
    if r==4:
     check(residual==(15*K**4+30*K*K*U+5*U*U+2*V)/5760,('quartic residual',a,N,k));centerchecks+=1
    if r==5:
     check(residual==-K*(3*K**4+10*K*K*U+5*U*U+2*V)/11520,('quintic residual',a,N,k));centerchecks+=1
    if r%2 and not K:
     check(not residual,('physical reflection',a,N,r,k));reflectionchecks+=1
out={'quartics':quartics,'direct_differentiation_checks':checks,'centered_r4_r5_checks':centerchecks,'physical_reflection_checks':reflectionchecks,'parameters':[str(a) for a in params],'max_order':MAXN,'max_defect':MAXR,'all_checks_pass':True}
Path(__file__).with_name('replay_independent.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
