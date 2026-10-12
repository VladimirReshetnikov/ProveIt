"""Independent confluent grading, ensemble and double-pole checks.

Uses no delivered modules. Finite exact certificates support the canonical
proof; they do not establish the infinite compiler or minimal period weight.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product, combinations
from math import prod, comb, factorial
import json,sys,time
import sympy as S
import mpmath as mp
if sys.flags.optimize:raise RuntimeError('Assertions must remain enabled')
V=Path(__file__).resolve().parent;start=time.monotonic();x=S.Symbol('x')
profiles=[('polynomial',x*x-x+1,{}),('simple',1/x,{0:[1]}),
 ('double',1/x**2,{0:[0,1]}),('triple',1/x**3,{0:[0,0,1]}),
 ('confluent-mixed',1/x**4+1/(x+3),{0:[0,0,0,1],3:[1]}),
 ('shifted-mixed',1/(x+1)**2+2/(x+4),{1:[0,1],4:[2]}),
 ('separated-simple',1/x-3/(x+2)+5/(x+5),{0:[1],2:[-3],5:[5]}),
 ('polynomial-confluent',x*x+1/x**2-2/(x+2)**2,{0:[0,1],2:[0,-2]})]
def determinant(mat):
 a=[list(map(Q,row)) for row in mat];n=len(a);d=Q(1)
 for i in range(n):
  p=next((j for j in range(i,n) if a[j][i]),None)
  if p is None:return Q(0)
  if p!=i:a[i],a[p]=a[p],a[i];d=-d
  v=a[i][i];d*=v
  for j in range(i+1,n):
   t=a[j][i]/v
   for k in range(i+1,n):a[j][k]-=t*a[i][k]
 return d
def budget(sizes,r):
 return sum(sorted((s-2*k for s in sizes for k in range(s) if s-2*k>0),reverse=True)[:r])
allocation=[]
for n in range(1,4):
 for sizes in product(range(1,8),repeat=n):
  for r in range(7):
   b=max(sum(k*(s-k+1) for k,s in zip(ks,sizes)) for ks in product(*(range(s+1) for s in sizes)) if sum(ks)<=r)
   assert b==budget(sizes,r)
   allocation.append(dict(sizes=sizes,rank=r,budget=b))
print('Allocation cases',len(allocation),'PASS',flush=True)
grading=[];ensemble_checks=0;matrix_entries=0
for name,R,poles in profiles:
 symbols={(a,p):S.Symbol(f'h{a}_{p}') for a,cs in poles.items() for p in range(1,len(cs)+1)}
 moment=[];polynomial=[]
 for j in range(7):
  residual=S.apart(x**j*R,x);form=0
  for (a,p),h in symbols.items():
   c=S.expand(S.diff(S.cancel((x+a)**len(poles[a])*x**j*R),x,len(poles[a])-p).subs(x,-a))/factorial(len(poles[a])-p)
   form+=c*h;residual-=c/(x+a)**p
  residual=S.cancel(residual);assert residual.is_polynomial(x)
  value=sum(residual.subs(x,n) for n in range(1,8))
  moment.append(S.expand(value+form));polynomial.append(value)
 for r in range(1,5):
  direct=S.Matrix(r,r,lambda i,j:moment[i+j]);block=S.Matrix(r,r,lambda i,j:polynomial[i+j])
  for a,cs in poles.items():
   size=len(cs);va=S.Matrix(r,size,lambda i,p:comb(i,p)*(-a)**(i-p) if p<=i else 0)
   ca=S.Matrix(size,size,lambda p,q:sum(cs[ell-1]*symbols[a,ell-p-q] for ell in range(p+q+1,size+1)))
   block+=va*ca*va.T
  assert direct==block;matrix_entries+=r*r
  det=S.expand(direct.det(method='domain-ge'))
  weights=[p for a,p in symbols];b=budget([len(cs) for cs in poles.values()],r)
  terms=S.Poly(det,*symbols.values()).terms() if symbols else [((),det)]
  observed=max((sum(e*w for e,w in zip(a,weights)) for a,c in terms if c),default=0)
  assert observed<=b
  grading.append(dict(profile=name,rank=r,cutoff=7,budget=b,observed_weight=observed,monomials=len(terms),passed=True))
  print(name,'rank',r,'formal weight',observed,'<=',b,'PASS',flush=True)
 values=[Q(R.subs(x,n)) for n in range(1,9)]
 for M in range(9):
  for r in range(1,6):
   moments=[sum((Q(n)**j*values[n-1] for n in range(1,M+1)),Q(0)) for j in range(2*r-1)]
   d=determinant([[moments[i+j] for j in range(r)] for i in range(r)])
   v=sum((prod(Q(b-a)**2 for a,b in combinations(nodes,2))*prod(values[n-1] for n in nodes) for nodes in combinations(range(1,M+1),r)),Q(0))
   assert d==v
   if M<r:assert d==0
   ensemble_checks+=1
N=42;L=[Q(0)]+[Q(1,n) for n in range(1,N+1)];Li=[Q(0)]+[Q(1,n*n) for n in range(1,N+1)]
L2=[sum((L[k]*L[n-k] for k in range(n+1)),Q(0)) for n in range(N+1)]
num=[Q(0)]*(N+1)
for n in range(N+1):
 num[n]=-2*Li[n]+3*L[n]-L2[n]
 if n:num[n]+=3*Li[n-1]-3*L[n-1]+L2[n-1]
 if n==1:num[n]-=1
assert num[:3]==[0,0,0]
double=[]
for M in range(41):
 h=sum((Q(1,n) for n in range(1,M+2)),Q(0))-1
 h2=sum((Q(1,n*n) for n in range(1,M+2)),Q(0))-1
 expected=M*h2-h*h;actual=sum((Q(M+2-k)*num[k] for k in range(M+2)),Q(0))
 assert actual==expected
 double.append(dict(cutoff=M,coefficient=str(actual),passed=True))
controls=dict(triple_pole_order_is_not_budget=grading[13]['observed_weight']==4 and grading[13]['observed_weight']>3,
 ordered_ensemble_has_no_factorial=determinant([[sum(Q(1,n*n) for n in range(2,5)),sum(Q(1,n) for n in range(2,5))],[sum(Q(1,n) for n in range(2,5)),Q(3)]])!=2*(3*sum(Q(1,n*n) for n in range(2,5))-sum(Q(1,n) for n in range(2,5))**2),
 empty_word_anchor_rejects_log_pole=S.residue(1/(x*(1-x)),x,0)==1 and S.residue((x/(1-x))/x,x,0)==0,
 wrong_dilog_numerator_rejected=num[1]+Li[1]!=0)
assert all(controls.values())
mp.mp.dps=80;numeric=[]
for z in [mp.mpf('.2'),mp.mpf('.7'),mp.mpc('.25','.12')]:
 l=-mp.log1p(-z);closed=((3*z-2)*mp.polylog(2,z)+(1-z)*(3*l-l*l)-z)/(z*(1-z)**2)
 total=mp.mpc(0);h=mp.mpf(0);h2=mp.mpf(0)
 for M in range(1,801):
  h+=mp.mpf(1)/(M+1);h2+=mp.mpf(1)/(M+1)**2;total+=(M*h2-h*h)*z**M
 error=abs(closed-total);assert error<mp.mpf('1e-70')
 numeric.append(dict(z=str(z),error=mp.nstr(error,25),terms=800,passed=True))
# Integrate the ordinary endpoint after its cancellation; diagnostic only.
def endpoint_integrand(z):
 if z==0:return mp.mpf(0)
 if z==1:return (mp.zeta(2)-1)/2
 l=-mp.log1p(-z);return ((3*z-2)*mp.polylog(2,z)+(1-z)*(3*l-l*l)-z)/(2*z*z)
q=mp.quad(endpoint_integrand,[0,mp.mpf('.25'),mp.mpf('.75'),1]);rhs=mp.mpf(5)*mp.zeta(3)/2-mp.mpf(3)*mp.zeta(2)/2-mp.mpf(1)/2
err=abs(q-rhs);assert err<mp.mpf('1e-65')
out=dict(status='PASS',imports_delivered_code=False,exact_allocation_cases=len(allocation),formal_grading_cases=len(grading),matrix_entry_checks=matrix_entries,ensemble_checks=ensemble_checks,double_pole_Taylor_coefficients=len(double),grading=grading,double_pole=double,corruption_controls=controls,working_digits=80,numeric_generators=numeric,endpoint_error=mp.nstr(err,25),interval_certified=False,seconds=time.monotonic()-start,
 scope='Independent finite exact polynomial grading and node sums; floating-point generator/endpoint diagnostics are not proofs or interval certificates. Written confluent/anchored-integration proofs establish all ranks.')
(V/'hankel-alphabet-checks.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print('Hankel alphabet independent checks PASS',flush=True)
