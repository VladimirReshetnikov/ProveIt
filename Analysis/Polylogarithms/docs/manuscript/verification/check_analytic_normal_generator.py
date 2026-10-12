"""Independent IBP/Beta coefficient and analytic-jet generator diagnostics.

No delivered program is imported. The analytic convergence argument is
written separately; numerical comparisons are not interval certificates.
"""
from pathlib import Path
from functools import lru_cache
from fractions import Fraction as Q
from math import factorial,comb
import json,sys,time
import mpmath as mp
if sys.flags.optimize:raise RuntimeError('Assertions must be enabled.')
V=Path(__file__).resolve().parent;started=time.monotonic()
def trim(a):
 a=list(a)
 while a and not a[-1]:a.pop()
 return tuple(a)
def add(p,q,scale=Q(1)):
 out=dict(p)
 for a,c in q.items():out[a]=out.get(a,Q(0))+scale*c
 return {a:c for a,c in out.items() if c}
def derivative(p):
 out={}
 for a,c in p.items():
  for j,n in enumerate(a):
   if not n:continue
   b=list(a)+[0];b[j]-=1;b[j+1]+=1;b=trim(b);out[b]=out.get(b,Q(0))+n*c
 return out
@lru_cache(None)
def normal(a):
 if len(a)<2 or a[-1]>=2:return ((a,Q(1)),)
 r=len(a)-1;b=list(a);b[r]-=1;b[r-1]+=1;b=trim(b);multiplicity=b[r-1]
 terms=derivative({b:Q(1)});assert terms.pop(a)==multiplicity;out={}
 for key,c in terms.items():out=add(out,dict(normal(key)),-c/multiplicity)
 return tuple(out.items())
def multiply(p,q):
 out=[Q(0)]*(len(p)+len(q)-1)
 for i,x in enumerate(p):
  for j,y in enumerate(q):out[i+j]+=x*y
 return out
@lru_cache(None)
def C(r):return tuple(Q(1,2**r*factorial(j)*factorial(r+1-j)) if j%2==r%2 else Q(0) for j in range(r+1))
def beta_coefficient(a):
 if len(a)<2:return Q(1)
 r=len(a)-1
 if a[r]<2 or sum(j*n for j,n in enumerate(a))%2:return Q(0)
 weight=sum((j+1)*n for j,n in enumerate(a));p=[Q((-1)**(j//2)*comb(r,j//2)) if j%2==0 else Q(0) for j in range(2*r+1)]
 for j in range(1,r+1):
  for _ in range(a[j]-(2 if j==r else 0)):p=multiply(p,C(j))
 integral=sum(c/Q(j+1) for j,c in enumerate(p))
 return Q((-1)**r*factorial(weight),4**r*factorial(r)*factorial(r+1))*integral/Q(factorial(a[0]))/Q(__import__('math').prod(factorial(n) for n in a[1:]))
raw={():Q(1)};forms=[raw];comparisons=0;normalization=[]
for weight in range(1,19):
 next_raw={}
 for a,c in raw.items():b=list(a or (0,));b[0]+=1;next_raw[tuple(b)]=c
 raw=add(next_raw,derivative(raw),Q(-1));nf={}
 for a,c in raw.items():nf=add(nf,dict(normal(a)),c)
 for a in set(raw)|set(nf):assert beta_coefficient(a)==nf.get(a,Q(0)),(weight,a);comparisons+=1
 forms.append(nf);normalization.append(dict(weight=weight,raw_monomials=len(raw),canonical_monomials=len(nf),passed=True))
 print('Independent canonical/Beta coefficient weight',weight,'PASS',flush=True)
# Kernel endpoint and coefficient bounds are exact finite diagnostics;
# the proof establishes them at every derivative index.
for r in range(1,25):assert sum(C(r))==Q(1,factorial(r+1))
affine_coefficient_checks=0
for m in range(19):
 expected={trim((m,)):Q(1)}
 for k in range(1,m//4+1):expected[trim((m-4*k,2*k))]=-Q(factorial(m),factorial(m-4*k)*4**k*(2*k-1)*(2*k+1)*factorial(2*k))
 assert {a:c for a,c in forms[m].items() if len(a)<=2}==expected
 affine_coefficient_checks+=1
mp.mp.dps=75
def cm(r,v):return sum(mp.mpf(c.numerator)/c.denominator*v**j for j,c in enumerate(C(r)))
def E2(z):
 if not z:return mp.mpf('0.5')
 if abs(z)<mp.mpf('0.01'):
  return sum(z**j/mp.factorial(j+2) for j in range(42))
 return (mp.expm1(z)-z)/z**2
def projection(jets,t,d):
 answer=mp.mpc(1)
 for r in range(1,d+1):
  xr=jets[r]*t**(r+1)
  if not xr:continue
  coefficient=mp.mpf((-1)**r)/(4**r*mp.factorial(r)*mp.factorial(r+1))
  def integrand(v):
   exponent=sum(cm(j,v)*jets[j]*t**(j+1) for j in range(1,r))
   return (1-v*v)**r*mp.exp(exponent)*E2(cm(r,v)*xr)
  answer+=coefficient*xr*xr*mp.quad(integrand,[-1,0,1])/2
 return mp.exp(jets[0]*t)*answer
def polynomial_value(nf,jets,d):
 return sum(mp.mpf(c.numerator)/c.denominator*mp.fprod(jets[j]**n for j,n in enumerate(a)) for a,c in nf.items() if len(a)<=d+1)
cases=[('Gamma-real',mp.mpf('1.3'),mp.mpf('0.03'),mp.mpf(1),mp.mpf(9)),('Gamma-complex',mp.mpc(2,'0.1'),mp.mpc('0.02','0.01'),mp.mpf(1),mp.mpf(9)),('exponential',mp.mpf(0),mp.mpf('0.04'),mp.mpf(1),mp.mpf(3)),('quadratic',mp.mpf('0.3'),mp.mpf('0.05'),mp.mpf(1),mp.mpf(3)),('simple-pole',mp.mpf(1),mp.mpf('0.025'),mp.mpf('0.5'),mp.mpf(2))]
checks=[]
for name,x,t,rho,M in cases:
 if name.startswith('Gamma'):jets=[mp.digamma(x)]+[mp.polygamma(r,x) for r in range(1,19)]
 elif name=='exponential':jets=[mp.exp(x)]*19
 elif name=='quadratic':jets=[x*x+1,2*x,mp.mpf(2)]+[mp.mpf(0)]*16
 else:jets=[(-1)**(r+1)*mp.factorial(r)/x**(r+1) for r in range(19)]
 values={d:projection(jets,t,d) for d in (1,2,3,5,8)}
 for d in (1,2,3,5):
  partial=sum(polynomial_value(forms[m],jets,d)*t**m/mp.factorial(m) for m in range(19))
  err=abs(values[d]-partial);assert err<mp.mpf('1e-25'),(name,d,err)
  q=abs(t)/rho;s=q*q/4;tail=M*M*abs(t)**2*mp.exp(M*abs(t)/(1-q))*s**(d+1)/(2*(d+2)*(1-s))
  difference=abs(values[8]-values[d]);assert difference<=tail,(name,d,difference,tail)
  checks.append(dict(case=name,input_point=str(x),t=str(t),cauchy_radius=str(rho),cauchy_M_bound=str(M),projection=d,series_weight_cutoff=18,series_error=mp.nstr(err,24),finite_projection_difference=mp.nstr(difference,24),proved_tail_majorant=mp.nstr(tail,24),passed=True))
 print(name,'ordinary projection and analytic-jet diagnostics PASS',flush=True)
missing_linear=mp.quad(lambda v:(1-v*v)**2/(8*(1+3*v*v)),[0,1])
assert missing_linear>0 and abs(missing_linear-(-mp.mpf(1)/12+2*mp.pi/(27*mp.sqrt(3))))<mp.mpf('1e-70')
assert forms[3].get((0,0,1),Q(0))==0
affine=[]
for a,b,t in [(mp.mpf('1.5'),mp.mpf(2)/3,mp.mpf(1)/8),(mp.mpc(1,'0.2'),mp.mpc('0.4','0.1'),mp.mpc('0.1','-0.05'))]:
 z=b*t*t/2;shi=mp.quad(lambda v:mp.sinh(z*v)/v if v else z,[0,1])
 closed=mp.exp(a*t)*(mp.cosh(z)+mp.sinh(z)/z-z*shi)/2
 ordinary=projection([a,b]+[mp.mpf(0)]*17,t,1);error=abs(closed-ordinary);assert error<mp.mpf('1e-70')
 affine.append(dict(u0=str(a),u1=str(b),t=str(t),error=mp.nstr(error,24),passed=True))
out=dict(status='PASS',imports_delivered_code=False,exact_coefficient_comparisons=comparisons,weights=[0,18],normalization_checks=normalization,endpoint_polynomial_bounds_checked=24,affine_coefficient_checks=affine_coefficient_checks,working_digits=75,numerical_diagnostics=checks,affine_closed_generator_diagnostics=affine,interval_certified=False,missing_linear_subtraction_control=dict(rejected=True,wrong_unique_u2_coefficient=mp.nstr(missing_linear,32),closed_value='-1/12 + 2*pi/(27*sqrt(3))',correct_coefficient='0'),elapsed_seconds=round(time.monotonic()-started,3),scope='Independent sparse canonical integration by parts versus the universal Beta coefficient formula through weight eighteen. Ordinary finite-projection integrals are compared with independent normalized Taylor polynomials and the analytically proved tail majorant; the closed affine generator and its coefficient formula are checked independently. Omitting the linear subtraction produces a forbidden nonzero unique-highest-variable coefficient. Numerical comparisons do not establish the infinite theorem or certify intervals.')
(V/'analytic-normal-generator-checks.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print('Analytic normal-generator audit PASS',flush=True)
