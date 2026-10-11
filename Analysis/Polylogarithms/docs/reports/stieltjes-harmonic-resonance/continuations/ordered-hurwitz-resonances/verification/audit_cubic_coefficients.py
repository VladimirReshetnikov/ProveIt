"""Independent exact coefficient audit of cubic Hurwitz/Tornheim formula."""
from pathlib import Path
import json
import sympy as S

t=S.symbols('t')
g,L,g1,g2,z2,z3,z21,T0,T1,T2,T3=S.symbols('gamma ell gamma1 gamma2 zeta2 zeta3 zeta2prime tau0 tau1 tau2 tau3')
Z=1+g*t-g1*t**2+g2*t**3/2
A=1+2*z2*t**2-2*z3*t**3
b1=3*(g+L);b2=S.Rational(3,4)*z2;b3=z3
B=1+b1*t+(b1**2/2+b2)*t**2+(b1**3/6+b1*b2+b3)*t**3
Tau=T0-T1*t+T2*t**2/2-T3*t**3/6
N=S.expand(-6*B*Tau+3*A*Z.subs(t,2*t)-1+3*(Z-1)**2)
a0=-z2;a1=-z2-z21
sol={T0:S.Rational(1,3),T1:L,T2:3*L**2-2*g**2-4*g1+z2}
checks={
 'third_order_pole':S.expand(N.coeff(t,0).subs(sol))==0,
 'second_order_pole':S.expand(N.coeff(t,1).subs(sol))==0,
 'first_order_pole':S.expand(N.coeff(t,2).subs(sol)+S.Rational(3,2)*a0)==0,
}
I=S.expand(-N.coeff(t,3).subs(sol)-S.Rational(3,2)*a1)
want=-T3-9*g**3-18*g**2*L-30*g*g1-36*L*g1-12*g2+9*L**3+S.Rational(3,2)*g*z2+9*L*z2+S.Rational(3,2)*z2+8*z3+S.Rational(3,2)*z21
checks['cubic_finite_part_all_coefficients']=S.expand(I-want)==0
# The four independent Mellin counterterms in C6 have exponents below.
s=S.symbols('s')
checks['mellin_counterterm_exponents']=[S.expand(e) for e in [(s-1)+(2*s-2)+1,(s-1)+(s-1)+1,(s-1)+s+1,(s-1)+1]]==[3*s-2,2*s-1,2*s,s]
assert all(checks.values()),checks
out={'arithmetic':'exact symbolic polynomial/rational','checks':checks,'passed':sum(checks.values())}
(Path(__file__).resolve().parent.parent/'results'/'cubic_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
