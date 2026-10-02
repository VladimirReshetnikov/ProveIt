#!/usr/bin/env python3
"""Independent exact fourth-scale check using beta derivatives and series composition.

No sequence-value fitting and no coefficient/action reduction is used.
Run: python verify_action_coefficients.py
"""
import sympy as S

x, ell, c, d, u1, u2 = S.symbols('x ell c d u1 u2')
g = S.log(2)

def trunc(expr, n=3):
    return S.expand(S.series(expr, x, 0, n).removeO())

def moment(sign, r, m):
    """Integral of w_sign(z) log(z)^m / (1-z)^r, m>=r.

    Beta recurrence is applied BEFORE differentiation to avoid artificial
    polygamma singularities at a+b=0,-1,... .
    """
    a = S.Symbol('a', positive=True)
    a0, b0 = ((S.Rational(3, 2), S.Rational(1, 2)) if sign == -1
              else (S.Rational(1, 2), S.Rational(3, 2)))
    b = b0-r
    beta = S.gamma(a)*S.gamma(b0)/S.gamma(a+b0)
    for j in range(r):
        beta *= (a+b+j)/(b+j)
    return S.simplify(S.expand_func(S.diff(beta, a, m).subs(a, a0)))

I0 = S.pi/2
J1, J2 = moment(-1, 1, 1), moment(-1, 2, 2)
K1, K2 = moment(+1, 1, 1), moment(+1, 2, 2)
assert S.simplify(J1+2*S.pi*(1-g)) == 0
assert S.simplify(J2-8*S.pi*(1-g)/3) == 0
assert S.simplify(K1+2*S.pi*g) == 0
assert S.simplify(K2-8*S.pi*g) == 0
print('PASS: four beta-log integrals derived independently')
for name, val in [('J1', J1), ('J2', J2), ('K1', K1), ('K2', K2)]:
    print(name, '=', val)

# tau=x*T with T=2L/3+ell/3+d+u1/L+u2/L^2, x=1/L.
tau = S.Rational(2,3)+x*(ell/3+d)+u1*x*x+u2*x**3
A = ell+trunc(S.log(tau))+c
# k(T)=T/2+A+(2A-3)/T+O(T^-2 log(T)^2).
kx = trunc(tau/2+x*A+x*x*(2*A-3)/tau)
# a=k'(T)/k(T); omitted k''/k first contributes at L^-3.
a = trunc(x*(S.Rational(1,2)+x/tau)/kx)
Im = trunc(1+S.binomial(-S.Rational(1,2),1)*J1/I0*a
             +S.binomial(-S.Rational(1,2),2)*J2/I0*a*a)
Ip = trunc(1+S.binomial(S.Rational(1,2),1)*K1/I0*a
             +S.binomial(S.Rational(1,2),2)*K2/I0*a*a)

# Constants fixed by Y0^3=2v alpha/(3 pi^2), d=log Y0.
# These equations follow directly from the original duration and action.
log_duration = trunc(S.Rational(3,2)*(u1*x+u2*x*x)
                     -S.log(3*kx)/2+S.log(Im))
usol1 = S.solve(log_duration.coeff(x,1),u1)[0]
usol2 = S.solve(log_duration.coeff(x,2).subs(u1,usol1),u2)[0]
assert S.simplify(log_duration.subs({u1:usol1,u2:usol2})) == 0
log_action = trunc((u1*x+u2*x*x)/2+S.log(3*kx)/2
                   +S.log((Im+2*Ip)/3))
log_action = S.expand(log_action.subs({u1:usol1,u2:usol2}))
b1 = S.simplify(log_action.coeff(x,1))
b2 = S.simplify(log_action.coeff(x,2)+b1*b1/2)
kappa = d-2*S.log(3)+2*c
B1 = kappa+S.Rational(7,3)*ell
B2 = -B1*B1/4+S.Rational(7,2)*B1-10
assert S.simplify(b1-B1) == 0
assert S.simplify(b2-B2) == 0
print('PASS: duration inversion and normalized action substitution')
print('kappa = d - 2 log(3) + 2 c')
print('B1 = kappa + 7 ell/3')
print('B2 = -B1^2/4 + 7 B1/2 - 10')
print('PASS: B2 matches the independently derived exact expression')
