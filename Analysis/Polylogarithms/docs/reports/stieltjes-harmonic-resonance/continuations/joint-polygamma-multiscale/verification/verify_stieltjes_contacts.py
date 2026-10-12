"""Independent algebra and quadrature checks of the collision identities."""
import json
from pathlib import Path

import mpmath as mp
import sympy as sp

from stieltjes_contacts import collision_correction, singular_contact

checks = 0
a, b = sp.symbols("a b", positive=True)


def equal(x, y):
    global checks
    if sp.simplify(x - y) != 0:
        raise AssertionError((x, y, sp.simplify(x - y)))
    checks += 1


# Independent route: differentiate the elementary logarithmic kernel term.
# The selected source-series index is r+j, not j.
for r in range(4):
    for t in range(3):
        for j in range(1, 4):
            term = a**(r + j) * b**(-r - j - 1) * sp.log(b / a)
            direct = sp.diff(term, a, r, b, t).subs({a: 2, b: 3})
            equal(singular_contact(0, 0, r, t, j, 2, 3), direct)

# Independent first-index route: inversion of the dilogarithm in E(a,b).
for j in range(1, 6):
    for lam, mu in [(1, 1), (2, 3)]:
        expected = (sp.Rational(lam, mu)**j / mu *
                    (sp.zeta(2) - sp.harmonic(j, 2) +
                     sp.harmonic(j) * sp.log(sp.Rational(lam, mu)) +
                     (sp.log(mu)**2 - sp.log(lam)**2) / 2))
        equal(singular_contact(1, 0, 0, 0, j, lam, mu), expected)

# Full formula against the independent integration-by-parts resonance law.
for alpha, beta in [(2, 1), (3, 1), (4, 1), (5, 1), (3, 2), (4, 3), (5, 2)]:
    q = sp.Rational(alpha, beta)
    j = 2 / (q - 1)
    for lam, mu in [(1, 1), (2, 3)]:
        expected = sp.zeta(2) * sp.log(sp.Rational(mu, lam))
        if q.q == 1:
            expected += (-1)**(int(q) + 1) * sp.Rational(mu**int(q), lam) * sp.zeta(q + 1)
        if j.q == 1:
            jj = int(j)
            expected += sp.Rational(lam**jj, mu**(jj + 2)) * ((jj + 1) * sp.log(sp.Rational(mu, lam)) - 1)
        equal(collision_correction(0, 0, 1, 0, alpha, beta, lam, mu) + sp.zeta(2), expected)

# Exact fixed-rate compatibility with the previous contact polynomial.
u = sp.Symbol('u')
for r in range(4):
    for m in range(3):
        rate = sp.Rational(2)
        other = sp.Rational(3)
        prior = (-1)**r * sp.rf(1+u, r)/sp.factorial(r) * (
            (rate**(-u)-1)/u + rate**(-u) * sum(
                sp.binomial(r,j)*(other/rate-1)**j/(u+j) for j in range(1,r+1)))
        # Contact with a constant analytic germ: use the equivalent finite
        # expansion at x=0 rather than spectral zeta coefficients.
        new = (-1)**r*(rate**(-u)-sp.rf(1+u,r)/sp.factorial(r))/u
        new += (-1)**r*sum(sp.rf(1+u,r-k-1)*rate**(k-r-u)*other**(r-k)/sp.factorial(r-k)
                           for k in range(r))
        equal(sp.expand(sp.series(prior-new,u,0,m+2).removeO()).coeff(u,m), 0)

mp.mp.dps = 64
numeric = []


def kernel_series(r,t,u,v,a,b,terms=105):
    R = r+t+1
    ans = mp.mpc(0)
    for k in range(r):
        ans += ((-1)**(r+t+k) * mp.gamma(t+1+v+k) * mp.gamma(r+u-k) /
                (mp.gamma(1+u)*mp.gamma(1+v)) * a**(-r-u) * b**(-t-1-v) * (a/b)**k)
    for j in range(terms):
        ans += ((-1)**t * b**(-R-v) * (a/b)**j/(u*mp.gamma(1+v)) *
                (a**(-u)*mp.gamma(R+j+v)/mp.rf(1-u,j) -
                 b**(-u)*mp.gamma(1-u)*mp.gamma(R+j+u+v)/mp.factorial(j)))
    return ans


for r,t in [(0,0),(1,0),(0,2),(2,1),(3,2)]:
    uu=mp.mpc('0.13','0.04'); vv=mp.mpc('-0.11','0.03')
    aa=mp.mpf('0.2'); bb=mp.mpf('0.8')
    direct=(-1)**(r+t)*mp.rf(1+uu,r)*mp.rf(1+vv,t)*mp.quad(
        lambda x:(x+aa)**(-r-1-uu)*(x+bb)**(-t-1-vv),[0,aa,bb,1,mp.inf])
    via=kernel_series(r,t,uu,vv,aa,bb)
    error=abs(direct-via)/(1+abs(direct))
    if error >= mp.mpf('1e-48'):
        raise AssertionError((r,t,error))
    numeric.append({'test':'paired singular branches vs direct integral','r':r,'t':t,
                    'scaled_residual':mp.nstr(error,8)})

# Ordinary classical-polylogarithm primitive, independently integrated.
for zz in ['0.2','0.6','0.9']:
    z=mp.mpf(zz)
    direct=mp.quad(lambda x:(mp.zeta(2)*x-mp.polylog(2,x))/(x*(1-x)),[0,z])
    value=2*mp.zeta(3)-mp.polylog(3,z)-2*mp.polylog(3,1-z)+mp.log(1-z)*mp.polylog(2,1-z)
    error=abs(direct-value)
    assert error<mp.mpf('1e-55')
    numeric.append({'test':'classical contact primitive','z':zz,'absolute_residual':mp.nstr(error,8)})

result={'exact_assertions':checks,'working_decimal_digits':mp.mp.dps,
        'numerical_checks':numeric,'all_passed':True,
        'scope':'Exact algebra plus independent quadrature diagnostics; floating residuals are not certified bounds.'}
Path(__file__).with_name('stieltjes_contact_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
