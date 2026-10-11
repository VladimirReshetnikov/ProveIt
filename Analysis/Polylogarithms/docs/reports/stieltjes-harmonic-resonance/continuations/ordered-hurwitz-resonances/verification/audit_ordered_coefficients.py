"""Independent formal audit of ordered Hurwitz finite-part coefficients."""
from itertools import permutations
from pathlib import Path
import json
import sympy as S

y,t=S.symbols('y t')
g,g1,g2,g3,g4=S.symbols('g g1 g2 g3 g4')
z2,z3,z4,z5=S.symbols('z2 z3 z4 z5')
z21,z22,z23,z31,z32,z41=S.symbols('z21 z22 z23 z31 z32 z41')
z={1:g-g1*t+g2*t**2/2-g3*t**3/6+g4*t**4/24,
   2:z2+2*z21*t+2*z22*t**2+S.Rational(4,3)*z23*t**3,
   3:z3+3*z31*t+S.Rational(9,2)*z32*t**2,
   4:z4+4*z41*t,5:z5}
# Newton recursion, independent of direct exponentiation.
r={0:S.Integer(1)}
for d in range(1,6):
 r[d]=S.expand(sum((-1)**(m-1)*z[m]*r[d-m] for m in range(1,d+1))/d)

want={
(2,1):-g*g1-z21,
(3,1):-g**2*g1/2+g1*z2/2-g*z21+z31,
(2,2):(g1**2+g*g2)/2-z22,
(4,1):-g**3*g1/6+g*g1*z2/2-g**2*z21/2+z2*z21/2-g1*z3/3+g*z31-z41,
(3,2):g*g1**2/2+g**2*g2/4-g2*z2/4+g1*z21-g*z22+S.Rational(3,2)*z32,
(2,3):-g*g3/6-g1*g2/2-S.Rational(2,3)*z23,
}
checks={f'r{d}_coefficient_{k}':S.expand(r[d]).coeff(t,k)==S.expand(expr) for (d,k),expr in want.items()}
c1,c2,c3,eta=S.symbols('c1 c2 c3 eta',nonzero=True)
B3=g**3/6-g*z2/2+z3/3
def fp(a,b,c):
 return B3-c/a*(g*g1+z21)+c*c*g2/(2*a*(a+b))+(b-c)/a*eta
lhs=sum(fp(*p) for p in permutations((c1,c2,c3)))
cs=(c1,c2,c3)
expected=g**3-g*g1*sum(cs[i]/cs[j] for i in range(3) for j in range(3) if i!=j)
expected+=g2*S.Rational(1,2)*sum(cs[i]**2/(cs[(i+1)%3]*cs[(i+2)%3]) for i in range(3))
expected-=3*g*z2+z21*sum((sum(cs)-cs[i])/cs[i] for i in range(3))
expected+=2*z3
checks['arbitrary_depth3_full_stuffle_symmetrization']=S.factor(lhs-expected)==0
assert all(checks.values()),checks
out={'arithmetic':'exact symbolic polynomial/rational','checks':checks,'passed':sum(checks.values())}
(Path(__file__).resolve().parent.parent/'results'/'ordered_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
