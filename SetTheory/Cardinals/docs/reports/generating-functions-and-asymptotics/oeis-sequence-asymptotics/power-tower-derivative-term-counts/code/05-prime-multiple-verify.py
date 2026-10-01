"""Exact regression checks; the uniform theorem is proved in the article."""
from fractions import Fraction as Q
from math import factorial, comb
from pathlib import Path
import json

BASE=Path(__file__).resolve().parent
MAXR=72
h=[Q(1)]+[Q((-1)**(j-1),j*(j+1)) for j in range(1,MAXR+1)]
logh=[Q(0)]
for n in range(1,MAXR+1):
 logh.append(h[n]-sum((j*logh[j]*h[n-j] for j in range(1,n)),Q(0))/n)
polys=[[Q(1)]]
for n in range(1,MAXR+1):
 row=[Q(0)]*(n+1)
 for j in range(1,n+1):
  c=j*logh[j]/n
  for k,v in enumerate(polys[n-j]):row[k+1]+=c*v
 polys.append(row)
def modq(x,p):
 if x.denominator%p==0:raise RuntimeError(('not p-integral',x,p))
 return (x.numerator%p)*pow(x.denominator,-1,p)%p
def evaluate(f,x):
 v=Q(0)
 for c in reversed(f):v=v*x+c
 return v
def falling(n):
 f=[1]
 for j in range(n):
  g=[0]*(len(f)+1)
  for k,c in enumerate(f):g[k]-=j*c;g[k+1]+=c
  f=g
 return f
def valq(x,p):
 if not x:return 10**9
 a,b=abs(x.numerator),x.denominator;e=0
 while a%p==0:e+=1;a//=p
 while b%p==0:e-=1;b//=p
 return e
congruence=[];lift_checks=0
for p in [3,5,7,11,13,17,19]:
 for m in range(2,min(p,7)):
  r=m*(p-1)
  if r>MAXR:continue
  g=[p**m*c for c in polys[r]]
  target=[Q(c,factorial(m)) for c in falling(m)]+[Q(0)]*(r-m)
  if any(modq(a-b,p) for a,b in zip(g,target)):raise RuntimeError(('congruence',p,m))
  for j in range(1,m):
   v=valq(evaluate(g,j),p)
   if v<m-j+1:raise RuntimeError(('lift',p,m,j,v))
   lift_checks+=1
  congruence.append({'p':p,'m':m,'r':r})
# Independent integer triangle recurrence, including the derivative bridge.
MAXM=400; pp=[1];prev=[0,1];nonzero=0;local_checks=0;bridge=0;triple=0;quadruple=0;cone=0
for M in range(2,MAXM+1):
 row=[0]*(M+1)
 for Y in range(1,M+1):
  row[Y]=(Y-M+1)*(prev[Y] if Y<len(prev) else 0)+prev[Y-1]+(M-1)*(pp[Y-1] if Y-1<len(pp) else 0)
  r=M-Y
  if 1<=r<=MAXR and M<=80:
   if row[Y]!=Q(factorial(M),factorial(Y))*evaluate(polys[r],Y):raise RuntimeError(('bridge',M,Y))
   bridge+=1
  if r>=1 and Y>=4*r:
   if row[Y]<=0:raise RuntimeError(('positivity cone',M,Y,row[Y]))
   cone+=1
  for p in [2,3,5,7,11,13,17,19,23,29,31,37,41,43]:
   if r==2*(p-1):
    if not row[Y]:raise RuntimeError(('m2 zero',M,Y,p))
    nonzero+=1
   if p>2 and r==3*(p-1):
    if not row[Y]:raise RuntimeError(('triple zero',M,Y,p))
    triple+=1
   if r==4*(p-1):
    if not row[Y]:raise RuntimeError(('quadruple zero',M,Y,p))
    quadruple+=1
   if p>2 and r%(p-1)==0:
    m=r//(p-1)
    if 2<=m<p and row[Y]==0 and not any((Y-j)%p**(m-j+1)==0 for j in range(1,m)):
     raise RuntimeError(('localization',M,Y,p,m))
    if 2<=m<p:local_checks+=1
 pp,prev=prev,row
prime_square=[]
for p in [2,3,5,7]:
 r=p*p-1;g=[p**(p+2)*c for c in polys[r][1:]]
 expected=[Q(0)]*len(g);expected[1]=Q(1);expected[p]=Q(-1)
 if any(modq(a-b,p) for a,b in zip(g,expected)):raise RuntimeError(('prime square',p))
 prime_square.append(p)
small_poly=[-122821584,172998164,-89214420,22538215,-3075240,229950,-8820,135]
if any(evaluate(small_poly,y)%11==0 for y in range(11)):raise RuntimeError('small certificate')
ratio=polys[8][1]/small_poly[0]
if polys[8][1:]!=[ratio*x for x in small_poly]:raise RuntimeError('small polynomial identity')
harmonic={}
def harmonic_n(n):return sum((Q(1,j) for j in range(1,n+1)),Q(0))
for m,p in [(2,11),(3,83),(3,89),(4,3001)]:
 r=m*(p-1);M0=p*p+1+r
 # The final linear-cone condition (A) is an integer inequality.
 A=p*p+1>=4*r
 B=harmonic_n(r-1)-harmonic_n(m-1)>=4*(m-2)
 if not A or not B:raise RuntimeError(('harmonic conditions',m,p,A,B))
 harmonic[f'{m},{p}']={'A':A,'B':B}
out={'maximum_polynomial_degree':MAXR,'prime_square_congruence_primes':prime_square,'congruence_cases':congruence,'small_exponent_lift_checks':lift_checks,'integer_triangle_max_row':MAXM,'coefficient_bridge_checks':bridge,'complete_m2_family_checks':nonzero,'complete_m3_family_checks':triple,'complete_m4_family_checks':quadruple,'positive_cone_checks':cone,'localization_checks':local_checks,'small_certificate_values':[int(evaluate(small_poly,y)%11) for y in range(11)],'harmonic_examples':harmonic,'all_pass':True}
(BASE/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='congruence_cases'},indent=2))
