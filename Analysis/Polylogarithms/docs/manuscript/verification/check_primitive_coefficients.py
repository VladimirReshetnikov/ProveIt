"""Independent exact IBP against the all-index primitive polynomial integral.

Compare every monomial, including support zeros at weight one, rather than
only observed nonzero terms. No delivered code or stored coefficient table
is imported. Infinite statements are proved separately in the manuscript.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial,comb,prod
from functools import lru_cache
import argparse,json,sys,time
import mpmath as mp
if sys.flags.optimize:raise RuntimeError('Assertions must remain enabled.')
V=Path(__file__).resolve().parent
def trim(a):
 a=list(a)
 while a and not a[-1]:a.pop()
 return tuple(a)
def add(p,q,scale=Q(1)):
 out=dict(p)
 for a,c in q.items():out[a]=out.get(a,Q(0))+scale*c
 return {a:c for a,c in out.items() if c}
def var(p,j):
 out={}
 for a,c in p.items():
  b=list(a)+[0]*max(0,j+1-len(a));b[j]+=1;out[tuple(b)]=c
 return out
def D(p):
 out={}
 for a,c in p.items():
  for j,n in enumerate(a):
   if n:
    b=list(a)+[0];b[j]-=1;b[j+1]+=1;b=trim(b);out[b]=out.get(b,Q(0))+n*c
 return out
@lru_cache(None)
def normal_pair(a):
 if len(a)<2 or a[-1]>=2:return {a:Q(1)},{}
 d=len(a)-1;b=list(a);b[d]-=1;b[d-1]+=1;b=trim(b);n=b[d-1]
 rest=D({b:Q(1)});assert rest.pop(a)==n
 normal={};primitive={b:Q(1,n)}
 for key,c in rest.items():
  nn,hh=normal_pair(key);normal=add(normal,nn,-c/n);primitive=add(primitive,hh,-c/n)
 return normal,primitive
def mul(p,q):
 out=[Q(0)]*(len(p)+len(q)-1)
 for i,x in enumerate(p):
  for j,y in enumerate(q):out[i+j]+=x*y
 return out
@lru_cache(None)
def C(r):return tuple(Q(1,2**r*factorial(j)*factorial(r+1-j)) if j%2==r%2 else Q(0) for j in range(r+1))
def integral_coefficient(a,m):
 if len(a)<2:return Q(-m,2) if m>=2 else Q(0)
 d=len(a)-1;p=[Q(comb(d+1,j)) for j in range(d+2)]
 for j in range(1,d+1):
  for k in range(a[j]-(1 if j==d else 0)):p=mul(p,C(j))
 assert all(c>=0 for c in p) and any(c>0 for j,c in enumerate(p) if j%2==0)
 value=sum(2*c/Q(j+1) for j,c in enumerate(p) if j%2==0)
 return Q((-1)**(1+sum(j*n for j,n in enumerate(a)))*factorial(m),2**(d+2)*factorial(d+1)*prod(factorial(n) for n in a))*value
a=argparse.ArgumentParser();a.add_argument('--max-weight',type=int,default=30);args=a.parse_args();assert args.max_weight>=18
started=time.monotonic();raw={():Q(1)};previous=raw;comparisons=0;positive=0;rows=[];forms=[];examples={}
for m in range(1,args.max_weight+1):
 raw=add(var(raw,0),D(raw),Q(-1));N={};H={}
 for key,c in raw.items():
  nn,hh=normal_pair(key);N=add(N,nn,c);H=add(H,hh,c)
 assert add(N,D(H))==raw and () not in H
 for key in previous:
  expected=integral_coefficient(key,m);actual=H.get(key,Q(0));assert expected==actual,(m,key,expected,actual)
  if m>=2:
   assert actual and actual*Q((-1)**(m-sum(key)))>0;positive+=1
  comparisons+=1
 assert set(H)<=set(previous)
 rows.append(dict(weight=m,compared=len(previous),nonzero=len(H),passed=True));forms.append(H)
 if m<=18:
  for key,c in H.items():
   if m in (3,4,6,7):examples[str(m)+':'+str(key)]=str(c)
 print('Primitive coefficient integral weight',m,len(previous),'PASS',flush=True);previous=raw
# Structural controls distinguish this kernel from the normal-coefficient one.
assert integral_coefficient((0,1),3)==1 and 2*integral_coefficient((0,1),3)!=1
assert integral_coefficient((0,0,1),4)==-1
assert integral_coefficient((0,1,1),6)==9
assert integral_coefficient((0,1,0,1),7)==-14
assert integral_coefficient((),1)==0
mp.mp.dps=75
def cm(r,v):return sum(mp.mpf(c.numerator)/c.denominator*v**j for j,c in enumerate(C(r)))
def E1(z):return mp.expm1(z)/z if z else mp.mpf(1)
def projection(jets,t,d):
 value=mp.mpc('0.5')
 for r in range(1,d+1):
  Yr=(-1)**r*jets[r]*t**(r+1)
  if not Yr:continue
  def f(v):
   exponent=sum(cm(j,v)*(-1)**j*jets[j]*t**(j+1) for j in range(1,r))
   return (1+v)**(r+1)*mp.exp(exponent)*E1(cm(r,v)*Yr)
  value+=Yr*mp.quad(f,[-1,0,1])/(2**(r+2)*mp.factorial(r+1))
 return t/2-t*mp.exp(t*jets[0])*value
def val(H,jets,d):
 return sum(mp.mpf(c.numerator)/c.denominator*mp.fprod(jets[j]**n for j,n in enumerate(key)) for key,c in H.items() if len(key)<=d+1)
diagnostics=[]
for name,x,t in [('Gamma-real',mp.mpf('1.3'),mp.mpf('0.025')),('Gamma-complex',mp.mpc(2,'0.1'),mp.mpc('0.02','0.01')),('quadratic',mp.mpf('0.3'),mp.mpf('0.025'))]:
 jets=[mp.digamma(x)]+[mp.polygamma(r,x) for r in range(1,19)] if name.startswith('Gamma') else [1+x*x,2*x,mp.mpf(2)]+[mp.mpf(0)]*16
 for d in [1,2,3,5]:
  exact_integral=projection(jets,t,d);series=sum(val(forms[m-1],jets,d)*t**m/mp.factorial(m) for m in range(1,19))
  error=abs(exact_integral-series);assert error<mp.mpf('1e-25'),(name,d,error)
  diagnostics.append(dict(case=name,x=str(x),t=str(t),projection=d,weight_cutoff=18,error=mp.nstr(error,25),passed=True))
record=dict(status='PASS',imports_delivered_code=False,maximum_weight=args.max_weight,complete_coefficient_comparisons=comparisons,nonzero_support_sign_checks=positive,highest_index=args.max_weight-2,weights=rows,examples=examples,controls=dict(wrong_power_of_two_rejected=True,wrong_reflection_sign_rejected=True,missing_unique_highest_support_rejected=True,weight_one_constant_rejected=True),working_digits=75,ordinary_projection_diagnostics=diagnostics,interval_certified=False,seconds=round(time.monotonic()-started,3),scope='Every weighted-partition monomial compared with independent recursive IBP, including full support/sign and zero-constant normalization. Twelve ordinary finite-projection integrals compared with independent Taylor coefficients. Numerical diagnostics are not interval certificates; the manuscript proves the all-weight formula and full-disk convergence separately.')
(V/'primitive-coefficient-checks.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8');print('All-index primitive coefficient audit PASS',flush=True)
