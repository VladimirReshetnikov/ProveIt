"""Exact algebra and exact-integer recurrence checks; no fitted constants."""
import sympy as s, math, json
from pathlib import Path
import os
P=Path(os.environ.get("HISTORIC_TREE_OUTPUT_DIR", Path(__file__).parent))
p,q,r=s.symbols('p q r',positive=True)
qs=4*r**2/3
pd=q-4*p**2/3; qd=1-5*p*q/3
V=s.Rational(5,6)*(p-r)**2+q-qs-qs*s.log(q/qs)
claimed=-s.Rational(20,9)*(p-r)**2*(p+r)-s.Rational(5,3)*r*(q-qs)**2/q
err=s.together(s.diff(V,p)*pd+s.diff(V,q)*qd-claimed)
num=s.fraction(err)[0]
lyapunov=s.rem(s.Poly(num,r),s.Poly(r**3-s.Rational(9,20),r)).is_zero
z=s.symbols('z');lam=(13+s.I*s.sqrt(71))/2
D=lambda v:(3-v)*(4-v)*(5-v)-120
factor=s.simplify(D(z)+(z+1)*(z-lam)*(z-s.conjugate(lam)))==0
coeff={(0,0):s.Integer(1),(1,0):s.Integer(1),(0,1):s.Integer(1)}
for d in range(2,5):
 for k in range(d+1):
  l=d-k
  val=60*sum(coeff[i,j]*coeff[k-i,l-j] for i in range(k+1) for j in range(l+1) if (i,j) not in ((0,0),(k,l)))/D(k*lam+l*s.conjugate(lam))
  coeff[k,l]=s.simplify(s.expand_complex(val))
conjugates=all(s.simplify(coeff[l,k]-s.conjugate(v))==0 for (k,l),v in coeff.items())
# An independent logarithmic-time energy identity.
w,v=s.symbols('w v',positive=True)
acc=-s.Rational(13,3)*v-s.Rational(40,9)*w+(2*w)**s.Rational(-1,2)
E=v**2/2+s.Rational(20,9)*w**2-s.sqrt(2*w)
energy=s.simplify(s.diff(E,w)*v+s.diff(E,v)*acc+s.Rational(13,3)*v**2)==0
h=[1,1,1]
for n in range(200):h.append(sum(math.comb(n,k)*h[k]*h[n-k] for k in range(n+1)))
# Independent exact ordinary EGF recurrence.
f=[s.Integer(1),s.Integer(1),s.Rational(1,2)]
for n in range(70):f.append(sum(f[k]*f[n-k] for k in range(n+1))/((n+1)*(n+2)*(n+3)))
egf=all(f[n]*math.factorial(n)==h[n] for n in range(len(f)))
record={'lyapunov_identity':lyapunov,'indicial_factorization':factor,'root_energy_identity':energy,'conjugate_coefficients':conjugates,'exact_egf_and_integer_recurrences_agree_through':len(f)-1,'exact_egf_recurrence':egf,'a11_equals_minus_one_seventh':coeff[1,1]==-s.Rational(1,7),'coefficients':{str(k):str(v) for k,v in coeff.items()},'radius_bound':'3<rho<5 from invariant rectangle p∈[3/5,1], q∈[12/25,1]','exact_first40':h[:40]}
assert all(record[k] for k in ('lyapunov_identity','indicial_factorization','root_energy_identity','conjugate_coefficients','exact_egf_recurrence','a11_equals_minus_one_seventh'))
(P/'symbolic_validation.json').write_text(json.dumps(record,indent=2)+'\n')
(P/'exact_values_0_202.json').write_text(json.dumps(h)+'\n')
print(json.dumps(record,indent=2))
