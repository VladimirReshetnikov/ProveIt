"""Independent free-ring reduction versus rational-input amplitude sectors.

Projection precedes specialization. Exact finite coefficient comparisons and
floating-point branch/antiderivative diagnostics are distinct from the
manuscript's analytic amplitude and differential-equation proofs.
"""
from pathlib import Path
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial,prod
import json,sys,time
import mpmath as mp
if sys.flags.optimize:raise RuntimeError('Assertions must remain enabled.')
V=Path(__file__).resolve().parent;started=time.monotonic()
def trim(a):
 a=list(a)
 while a and not a[-1]:a.pop()
 return tuple(a)
def add(p,q,scale=Q(1)):
 out=dict(p)
 for a,c in q.items():out[a]=out.get(a,Q(0))+scale*c
 return {a:c for a,c in out.items() if c}
def D(p):
 out={}
 for a,c in p.items():
  for j,n in enumerate(a):
   if n:
    b=list(a)+[0];b[j]-=1;b[j+1]+=1;b=trim(b);out[b]=out.get(b,Q(0))+n*c
 return out
def times_u0(p):
 out={}
 for a,c in p.items():b=list(a or (0,));b[0]+=1;out[tuple(b)]=c
 return out
@lru_cache(None)
def reduce(a):
 if len(a)<2 or a[-1]>=2:return {a:Q(1)},{}
 r=len(a)-1;b=list(a);b[r]-=1;b[r-1]+=1;b=trim(b);mult=b[r-1]
 rest=D({b:Q(1)});assert rest.pop(a)==mult
 normal={};primitive={b:Q(1,mult)}
 for key,c in rest.items():
  n,h=reduce(key);normal=add(normal,n,-c/mult);primitive=add(primitive,h,-c/mult)
 return normal,primitive
def amplitude(p,k):
 return sum(c*prod((-1)**(j*n)*factorial(j)**n for j,n in enumerate(a)) for a,c in p.items() if sum(a)==k)
raw={():Q(1)};rows=[];normal2=[];primitive2=[]
for m in range(1,31):
 raw=add(times_u0(raw),D(raw),Q(-1));N={};H={}
 for a,c in raw.items():n,h=reduce(a);N=add(N,n,c);H=add(H,h,c)
 assert add(N,D(H))==raw and () not in H
 n1=amplitude(N,1);h1=amplitude(H,1);n2=amplitude(N,2);h2=amplitude(H,2)
 expected=Q((-1)**(m//2-1)*factorial(m//2-1)**2) if m%2==0 else Q(0)
 assert n1==(1 if m==1 else 0)
 assert h1==(0 if m==1 else -factorial(m-2))
 assert n2==expected
 rising2=Q(factorial(m-1))*sum(Q(1,j) for j in range(1,m))
 assert n2+(1-m)*h2==rising2
 assert h2==(0 if m==1 else expected/Q(m-1)-Q(factorial(m-2))*sum(Q(1,j) for j in range(1,m)))
 rows.append(dict(weight=m,normal_linear=str(n1),primitive_linear=str(h1),normal_quadratic=str(n2),primitive_quadratic=str(h2),passed=True))
 normal2.append(n2/Q(factorial(m)));primitive2.append(h2/Q(factorial(m)))
 print('Rational-input free-ring amplitude weight',m,'PASS',flush=True)
mp.mp.dps=80
def functions(z):
 w=mp.asinh(z/2);y=z/(2+mp.sqrt(4+z*z));L=mp.log1p(-z)
 B=mp.polylog(2,y)-mp.polylog(2,-y)
 return 2*w*w,-z-(1-z)*L,-2*w*w+(1-z)*L*L/2-z*mp.polylog(2,z)+2*z*B
checks=[]
for z in [mp.mpf('0.2'),mp.mpf('0.75'),mp.mpc('0.25','0.15'),mp.mpc('-0.3','0.1')]:
 n,h1,h2=functions(z);L=mp.log1p(-z)
 e1=abs(h1-z*mp.diff(lambda q:functions(q)[1],z)-(-L-z))
 e2=abs(h2-z*mp.diff(lambda q:functions(q)[2],z)-(L*L/2-n))
 assert max(e1,e2)<mp.mpf('1e-70')
 checks.append(dict(z=str(z),linear_ODE_error=mp.nstr(e1,25),quadratic_ODE_error=mp.nstr(e2,25),passed=True))
taylor=[]
for z in [mp.mpf('0.04'),mp.mpc('0.03','0.01')]:
 n,_,h2=functions(z)
 eN=abs(n-sum(mp.mpf(a.numerator)/a.denominator*z**m for m,a in enumerate(normal2,1)))
 eH=abs(h2-sum(mp.mpf(a.numerator)/a.denominator*z**m for m,a in enumerate(primitive2,1)))
 assert max(eN,eH)<mp.mpf('1e-35')
 taylor.append(dict(z=str(z),normal_error=mp.nstr(eN,25),primitive_error=mp.nstr(eH,25),weight_cutoff=30,passed=True))
antiderivatives=[]
for x,t in [(mp.mpf(2),mp.mpf('0.6')),(mp.mpc(2,'0.2'),mp.mpc('0.5','-0.1'))]:
 def anti_asinh(v):
  z=t/v;w=mp.asinh(z/2);y=z/(2+mp.sqrt(4+z*z))
  return v*w*w-t*(mp.polylog(2,y)-mp.polylog(2,-y))
 def anti_log(v):
  z=t/v;return (v-t)*mp.log1p(-z)**2-2*t*mp.polylog(2,z)
 ea=abs(mp.diff(anti_asinh,x)-mp.asinh(t/(2*x))**2)
 el=abs(mp.diff(anti_log,x)-mp.log1p(-t/x)**2)
 assert max(ea,el)<mp.mpf('1e-70')
 antiderivatives.append(dict(x=str(x),t=str(t),asinh_error=mp.nstr(ea,25),log_error=mp.nstr(el,25),passed=True))
# Two normalizations cannot be recovered from the spatial ODE alone.
assert functions(mp.mpf('0.001'))[2]/mp.mpf('0.001')+1!=0
record=dict(status='PASS',imports_delivered_code=False,maximum_weight=30,coefficient_comparisons=120,weighted_defining_identity_checks=30,rows=rows,working_digits=80,ODE_diagnostics=checks,Taylor_diagnostics=taylor,antiderivative_diagnostics=antiderivatives,interval_certified=False,seconds=round(time.monotonic()-started,3),scope='Independent recursive reduction in the free ring before rational-input specialization. Four amplitude coefficient families checked at every weight through thirty, with the exact normalized decomposition and harmonic formula. Four real/complex ODE cases, two closed-form/Taylor cases and two paired antiderivative cases are numerical diagnostics, not certified enclosures. The manuscript proves the analytic sectors and local branches separately.')
(V/'rational-input-checks.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8');print('Rational-input amplitude and dilogarithm audit PASS',flush=True)
