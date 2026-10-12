"""Independent exact compensator construction and affine-generator controls.

No incoming code is imported. Numerical residuals are diagnostics, not
interval certificates; the analytic convergence proof is in the manuscript.
"""
from pathlib import Path
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial
import json,sys,time
import mpmath as mp
if sys.flags.optimize:raise RuntimeError('Assertions must remain enabled.')
started=time.monotonic();V=Path(__file__).resolve().parent
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
def partial(p,j):
 out={}
 for a,c in p.items():
  if j<len(a) and a[j]:
   b=list(a);b[j]-=1;out[trim(b)]=c*a[j]
 return out
def D(p):
 out={}
 for a,c in p.items():
  for j,n in enumerate(a):
   if n:
    b=list(a)+[0];b[j]-=1;b[j+1]+=1;b=trim(b);out[b]=out.get(b,Q(0))+n*c
 return out
@lru_cache(None)
def reduce_monomial(a):
 if len(a)<2 or a[-1]>=2:return {a:Q(1)},{}
 r=len(a)-1;b=list(a);b[r]-=1;b[r-1]+=1;b=trim(b);count=b[r-1]
 rest=D({b:Q(1)});assert rest.pop(a)==count
 n={};h={b:Q(1,count)}
 for key,c in rest.items():
  nn,hh=reduce_monomial(key);n=add(n,nn,-c/count);h=add(h,hh,-c/count)
 return n,h
def Euler(p):
 out={}
 for j in range(max(map(len,p),default=0)):
  q=partial(p,j)
  for k in range(j):q=D(q)
  out=add(out,q,Q((-1)**j))
 return out
def boundary(p):
 out={}
 for j in range(1,max(map(len,p),default=0)):
  q=partial(p,j)
  for k in range(j):
   out=add(out,var(q,j-1-k),Q((-1)**k));q=D(q)
 return out
def homotopy(p):return boundary({a:c/sum(a) for a,c in p.items()})
def h(j):return Q((-1)**(j+1),2**(j+1)*factorial(j+1))*(1+(Q(1,j*(j+2)) if j%2 else 0))
raw={():Q(1)};rows=[];affine=[];general_checks=0;H=[]
for m in range(19):
 if m:raw=add(var(raw,0),D(raw),Q(-1))
 n={};hh={}
 for a,c in raw.items():
  nn,hrec=reduce_monomial(a);n=add(n,nn,c);hh=add(hh,hrec,c)
 p=add(raw,n,Q(-1));closed=homotopy(p)
 assert closed==hh and add(n,D(hh))==raw and not Euler(p)
 assert add(var(Euler(p),0),D(boundary(p)))=={a:c*sum(a) for a,c in p.items()}
 assert () not in hh
 if m:
  expected_appell={():Q(-1)} if m==2 else {}
  assert add(partial(hh,0),H[m-1],Q(-m))==expected_appell
 H.append(hh);rows.append(dict(weight=m,raw_terms=len(raw),normal_terms=len(n),primitive_terms=len(hh),passed=True))
 expected={} if m<2 else {trim((m-2*j-1,j)):Q(factorial(m),factorial(m-2*j-1))*h(j) for j in range((m-1)//2+1)}
 actual={a:c for a,c in hh.items() if len(a)<=2}
 assert actual==expected,(m,actual,expected)
 affine.append(dict(weight=m,terms=len(actual),passed=True))
 if m<=10:
  for a in raw:
   monomial={a:Q(1)}
   assert add(var(Euler(monomial),0),D(boundary(monomial)))==({a:Q(sum(a))} if sum(a) else {})
   general_checks+=1
 print('Independent primitive weight',m,'PASS',flush=True)
assert not H[1] and h(0)==Q(-1,2)
assert boundary(add(raw,n,Q(-1)))!=H[-1]
mp.mp.dps=80;diagnostics=[]
for U,b,t in [(mp.mpf('0.7'),mp.mpf('0.4'),mp.mpf('0.003')),(mp.mpc('0.5','0.1'),mp.mpc('0.3','-0.05'),mp.mpc('0.002','0.001'))]:
 z=b*t*t/2;shi=mp.quad(lambda v:mp.sinh(z*v)/v if v else z,[0,1])
 F=(mp.cosh(z)+mp.sinh(z)/z-z*shi)/2
 closed=t/2+t*mp.exp(t*U)*(mp.exp(-z)-F)/(2*z)
 series=mp.mpc(0)
 for m,polynomial in enumerate(H):
  val=sum(mp.mpf(c.numerator)/c.denominator*U**(a[0] if a else 0)*b**(a[1] if len(a)>1 else 0) for a,c in polynomial.items() if len(a)<=2)
  series+=val*t**m/mp.factorial(m)
 error=abs(closed-series);assert error<mp.mpf('1e-40')
 diagnostics.append(dict(U=str(U),b=str(b),t=str(t),weight_cutoff=18,error=mp.nstr(error,25),passed=True))
tex=(V.parent/'chapters/07-universal-normal-generator.tex').read_text(encoding='utf-8')
assert '\\frac t2+t e^{tU(x)}' in tex and '\\mathsf H_1=0' in tex
record=dict(status='PASS',imports_delivered_code=False,weights=[0,18],exact_weight_checks=rows,generic_Euler_boundary_monomials=general_checks,primitive_Appell_identity_with_weight_two_anomaly=True,affine_coefficients=affine,constant_normalization_control=dict(rejected_missing_t_over_two=True,weight_one_primitive='0',wrong_weight_one_primitive='-1/2',printed_formula_bound=True),factor_degree_division_control_rejected=True,working_digits=80,affine_closed_diagnostics=diagnostics,interval_certified=False,elapsed_seconds=round(time.monotonic()-started,3),scope='Independent recursive canonical reduction with compensators versus factor-degree Euler homotopy, including every raw weight through eighteen and general monomial Euler-boundary identities through weight ten. The compensator Appell identity includes its weight-two constant anomaly. Complete affine coefficient formula and two closed-generator diagnostics; omission of t/2 violates zero-constant normalization. Finite checks support implementation; the manuscript proves the all-weight formula and analytic convergence separately.')
(V/'primitive-homotopy-checks.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print('Primitive homotopy audit PASS',flush=True)
