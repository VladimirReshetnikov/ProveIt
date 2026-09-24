#!/usr/bin/env python3
"""Optional symbolic/numerical audit. Requires sympy and mpmath.
The combinatorial proof and the standard-library verifier do not depend on these.
"""
import json
from fractions import Fraction
from pathlib import Path
import mpmath as mp
import sympy as sp
from research import compositions, refined_counts

ROOT = Path(__file__).resolve().parents[1]
x,y,v,z = sp.symbols('x y v z')
R = (2*x**2+x**3)/(1-x**2-x**3)
A = sp.factor(2*x*sp.diff(R,x)-8*x**2)
conjecture = -2*x**3*(4*x**5+8*x**4+4*x**3-9*x**2-8*x-3)/(x**3+x**2-1)**2
assert sp.cancel(A-conjecture) == 0
assert sp.gcd(sp.numer(A),sp.denom(A)) == 1
F = sp.factor(2*y**2*x*sp.diff((2*y*x**2+v*y**2*x**3)/(1-y*x**2-y**2*x**3),x)-8*y**3*x**2)
assert sp.cancel(F.subs({y:1,v:1})-A) == 0
Q = 1-y*x**2-y**2*x**3
B = 2*y**2*(2*y*x**2+v*y**2*x**3)/Q - 4*y**3*x**2
# [x^n]B equals f_n(y,v)/n, hence F=x*dB/dx.
assert sp.cancel(F-x*sp.diff(B,x)) == 0
# Small bivariate coefficients verified without relying on a GF fit.
series = sp.Poly(sp.series(F,x,0,16).removeO(), x)
for n in range(3,16):
    expected = sum((t+v*u)*y**d for d,(t,u) in refined_counts(n).items())
    assert sp.expand(series.nth(n)-expected) == 0
H = (2*z*x**2+3*z*x**3)/(1-z*x**2-z*x**3)-2*z*x**2
assert sp.cancel((8*z*sp.diff(H,z)-2*x*sp.diff(H,x)).subs(z,1)-A) == 0
# Exact matrix trace check of the Binet weights.
M = sp.Matrix([[0,0,1],[1,0,1],[0,1,0]])
I = sp.eye(3)
CM = (2*M+I)*(2*M+3*I).inv()
p = compositions(20)
for n in range(1,20):
    expected = (2*p[n-2] if n>=2 else 0)+(p[n-3] if n>=3 else 0)
    assert sp.trace(CM*(M**n)) == expected
# Exact rational certificate for the nearest-integer bound.
L,U = sp.Rational(13247,10000),sp.Rational(13248,10000)
f = z**3-z-1
assert f.subs(z,L) < 0 < f.subs(z,U)
assert (42*z**2-8*z-63).subs(z,L) > 0
C_exact = lambda a:(2*a+1)/(2*a+3)
assert 4-6*U**2+9*L > 0
assert sp.Rational(198,100) < C_exact(L)*L**4 < C_exact(U)*U**4 < 2
assert sp.Rational(263,100) < C_exact(L)*L**5 < C_exact(U)*U**5 < sp.Rational(264,100)
assert sp.Rational(150,100) < C_exact(L)*L**3 < C_exact(U)*U**3 < sp.Rational(151,100)
num,den = 4-2*z**2+z,4-6*z**2+9*z
assert sp.rem(z**6*den-16*num,f,z) == 42*z**2-8*z-63
# Analytic size cumulants; reduce expressions modulo the defining cubic.
t = sp.symbols('t')
mu_t = (1+2*t)/(2+3*t)
dt_ds = t*(1+t)/(2+3*t)
sigma_t = sp.diff(mu_t,t)*dt_ds
assert sp.factor(sigma_t-t*(1+t)/(2+3*t)**3) == 0
delta_t = 2+sp.diff(sp.log((2+t)/(2+3*t)),t)*dt_ds
for expr in [mu_t.subs(t,1/z)-(z+2)/(2*z+3),
             sigma_t.subs(t,1/z)-z**4/(2*z+3)**3,
             delta_t.subs(t,1/z)-(2-4*z**4/((2*z+1)*(2*z+3)**2))]:
    assert sp.rem(sp.fraction(sp.cancel(expr))[0],f,z) == 0

mp.mp.dps = 180
alpha = mp.findroot(lambda a:a**3-a-1,(mp.mpf('1.3'),mp.mpf('1.4')))
beta = -alpha/2+mp.j*mp.sqrt(1/alpha-alpha**2/4)
C = lambda a:(2*a+1)/(2*a+3)
mu = (alpha+2)/(2*alpha+3)
sigma2 = alpha**4/(2*alpha+3)**3
delta = 2-4*alpha**4/((2*alpha+1)*(2*alpha+3)**2)
p = compositions(1000)
for n in range(3,1001):
    a = 2*n*(2*p[n-2]+p[n-3])
    exact_binet = 2*n*(C(alpha)*alpha**n+2*mp.re(C(beta)*beta**n))
    assert abs(exact_binet-a) < mp.mpf('1e-45')
    if n>=4:
        assert int(mp.floor(C(alpha)*alpha**n+mp.mpf('0.5'))) == a//(2*n)
assert int(mp.floor(C(alpha)*alpha**3+mp.mpf('0.5'))) != 1
rows=[]
for n in [10,20,50,100,200,500,1000]:
    dist = {d:t+u for d,(t,u) in refined_counts(n).items()}
    tot = sum(dist.values())
    mean = Fraction(sum(d*c for d,c in dist.items()),tot)
    variance = Fraction(sum(d*d*c for d,c in dist.items()),tot)-mean*mean
    mean_mp = mp.mpf(mean.numerator)/mean.denominator
    var_mp = mp.mpf(variance.numerator)/variance.denominator
    rows.append({'n':n,'mean':mp.nstr(mean_mp,25),'mean_minus_mu_n':mp.nstr(mean_mp-mu*n,25),
                 'variance':mp.nstr(var_mp,25),'variance_over_n':mp.nstr(var_mp/n,25)})
report = {
 'sympy_version':sp.__version__, 'mpmath_version':mp.__version__, 'decimal_precision':mp.mp.dps,
 'gf_identity':'passed', 'trivariate_coefficients_checked_through_n':15,
 'rational_gf_reduced':'passed', 'perrin_weighting_identity':'passed',
 'exact_matrix_trace_binet_check':'passed', 'exact_rounding_bound_certificate':'passed',
 'binet_and_rounding_numeric_check_through_n':1000,
 'alpha':mp.nstr(alpha,65),'leading_constant_K':mp.nstr(2*C(alpha),65),
 'conjugate_C_modulus':mp.nstr(abs(C(beta)),65),
 'size_mean_slope_mu':mp.nstr(mu,65),'size_variance_slope_sigma2':mp.nstr(sigma2,65),
 'size_mean_intercept_delta':mp.nstr(delta,65),
 'limiting_unicyclic_probability':mp.nstr(1/(2*alpha+1),65),
 'size_moment_checks':rows,
 'rounding_rational_lower_bound':str((42*z**2-8*z-63).subs(z,L))
}
text=json.dumps(report,indent=2)+'\n'
(ROOT/'verification'/'symbolic_checks.json').write_text(text)
print(text,end='')
