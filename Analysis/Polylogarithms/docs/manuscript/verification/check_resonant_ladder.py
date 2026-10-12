"""Independent finite checks of the normalized resonant order ladder.

No delivered verifier is imported. Exact coefficient arithmetic checks the
two-index jet recurrence; direct exponentially convergent Lerch sums check
the analytic identity at nonintegral orders. These diagnostics do not replace
the all-order proof in TWENTY-FIRST-INTAKE-AUDIT.md.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial
import json,sys
import mpmath as mp
if sys.flags.optimize: raise RuntimeError('Assertions must remain enabled.')
V=Path(__file__).resolve().parent
exact=0
controls={'endpoint_cannot_be_omitted':False,
          'lower_jet_sign_cannot_flip':False,
          'factor_r_plus_one_cannot_be_r':False}
# Formal coefficients of D_(m-1)(e) zeta(1+e-n,a) are independent inputs.
# D_m=(1+e/m)D_(m-1). Check each basis vector, including the top jet.
for m in range(1,10):
 for n in range(1,16):
  for r in range(7):
   for j in range(r+1):
    coeff=lambda k: Q(1 if k==j else 0)
    c_m=Q((-1)**(n+r)*(r+1)*factorial(r)*factorial(m),factorial(m+n))*(coeff(r)+coeff(r-1)/m)
    c_prev=Q((-1)**(n+r)*(r+1)*factorial(r)*factorial(m-1),factorial(m+n-1))*coeff(r)
    lower=Q((-1)**(n+r-1)*r*factorial(r-1)*factorial(m-1),factorial(m+n-1))*coeff(r-1) if r else Q(0)
    assert (m+n)*c_m==m*c_prev-(r+1)*lower
    controls['lower_jet_sign_cannot_flip'] |= (m+n)*c_m!=m*c_prev+(r+1)*lower
    controls['factor_r_plus_one_cannot_be_r'] |= (m+n)*c_m!=m*c_prev-r*lower
    exact+=1
# The logarithmic core differentiates to m L^(r+1)-(r+1)L^r.
# At r=0 the second term is the separately required polynomial endpoint.
mp.mp.dps=85
primitive_cases=0
for m in range(9):
 for r in range(8):
  coefficients=[Q(0) for j in range(r+1)]
  endpoint=Q(0)
  for k in range(r+1):
   j=r-k
   c=Q(factorial(r+1),factorial(j+1)*(m+1)**(k+1))
   coefficients[j]+=(m+1)*c
   if j: coefficients[j-1]-=(j+1)*c
   else: endpoint-=c
  endpoint+=Q(factorial(r+1),(m+1)**(r+1))
  assert coefficients==[Q(int(j==r)) for j in range(r+1)] and endpoint==0
  primitive_cases+=1
iterated_cases=0
for m in range(6):
 for q in range(1,7):
  for r in range(7):
   h=[Q(1)]+[Q(0)]*(r+1)
   for i in range(1,q+1):
    x=Q(1,m+i)
    for j in range(1,r+2):h[j]+=x*h[j-1]
   A=Q(factorial(m+q),factorial(m))
   jets={r-j:Q(factorial(r+1),factorial(r-j+1))*h[j]/A for j in range(r+1)}
   polynomial=Q(factorial(r+1))*h[r+1]/A
   for k in range(m+q,m,-1):
    nextjets={}
    endpoint=k*polynomial
    for j,c in jets.items():
     nextjets[j]=nextjets.get(j,Q(0))+k*c
     if j:nextjets[j-1]=nextjets.get(j-1,Q(0))-(j+1)*c
     else:endpoint-=c
    jets={j:c for j,c in nextjets.items() if c}
    polynomial=endpoint
   assert jets=={r:Q(1)} and polynomial==0,(m,q,r,jets,polynomial)
   iterated_cases+=1
def psi(s,t,a):
 return mp.fsum(mp.exp(-(n+a)*t)/(n+a)**s for n in range(850))
def normal(m,e,t,a,derivative=False):
 d=mp.fprod(1+e/j for j in range(1,m+1))/mp.gamma(1-e)
 c=d*mp.zeta(1+e,a)-1/e
 if derivative:
  q=-psi(m+e,t,a)+mp.fsum(mp.zeta(m+e-j,a)*(-t)**j/mp.factorial(j) for j in range(m-1))
  return (-1)**m*mp.factorial(m)*d*q-m*t**(m-1)*c
 q=psi(m+1+e,t,a)-mp.fsum(mp.zeta(m+1+e-j,a)*(-t)**j/mp.factorial(j) for j in range(m))
 return (-1)**m*mp.factorial(m)*d*q-t**m*c
rows=[]
for m in range(1,5):
 for a in [mp.mpf('0.5'),mp.mpf(1),1+mp.j/5]:
  for e in [mp.mpf('0.125'),mp.mpf('-0.1')+mp.j/7]:
   t=mp.mpf('0.3')+mp.j/10
   lhs=normal(m,e,t,a,True)
   rhs=(m+e)*normal(m-1,e,t,a)-t**(m-1)
   err=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))
   assert err<mp.mpf('1e-70')
   controls['endpoint_cannot_be_omitted'] |= bool(abs(lhs-(m+e)*normal(m-1,e,t,a))>mp.mpf('1e-5'))
   rows.append(dict(m=m,a=str(a),epsilon=str(e),t=str(t),scaled_error=mp.nstr(err,12)))
assert all(controls.values())
result=dict(status='PASS',imports_delivered_code=False,exact_basis_cases=exact,
            exact_antiderivative_cases=primitive_cases,
            exact_iterated_primitive_cases=iterated_cases,
            maximum_m=9,maximum_tail_degree=15,maximum_jet_order=6,
            corruption_controls=controls,numerical_rows=rows,working_digits=85,
            defining_sum_terms=850,interval_certified=False,
            scope='Finite exact tail-coefficient basis checks and direct defining-sum diagnostics; all-index analytic proof recorded separately.')
(V/'resonant-ladder-checks.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS',exact,'exact coefficient basis cases;',primitive_cases,'single and',iterated_cases,'iterated primitives;',len(rows),'direct-sum diagnostics.')
