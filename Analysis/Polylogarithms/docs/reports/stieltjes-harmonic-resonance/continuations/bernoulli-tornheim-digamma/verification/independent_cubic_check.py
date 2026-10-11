"""Independent formal derivation of the printed three-ray cancellation.

Build Gamma and zeta Taylor series directly, without importing the complete
directional formula or the other verifier. Unresolved remainder derivatives
are removed solely by the axis and stuffle constraints.
"""
import json
from pathlib import Path
import sympy as s

t = s.Symbol('t')
g, z2, z3 = s.symbols('gamma zeta2 zeta3')
z01, z02, z03 = s.symbols('zeta_prime_0 zeta_second_0 zeta_third_0')
zm1, zm2, zm3 = s.symbols('zeta_prime_minus1 zeta_second_minus1 zeta_third_minus1')


def cut(poly):
    expanded = s.expand(poly)
    return sum(expanded.coeff(t, j)*t**j for j in range(4))


def expjet(v):
    return cut(1+v+v**2/2+v**3/6)


def zeta0(a):
    return -s.Rational(1, 2)+z01*a*t+z02*a*a*t*t/2+z03*a**3*t**3/6


def zetaminus1(a):
    return -s.Rational(1, 12)+zm1*a*t+zm2*a*a*t*t/2+zm3*a**3*t**3/6


def elementary_ray(a, b, c):
    a, b, c = map(s.Rational, (a, b, c))
    def gamma_ratio(v):
        return expjet(g*(v+c)*t+z2*(v*v-c*c)*t*t/2+z3*(v**3+c**3)*t**3/3)
    return cut(zeta0(a)*zeta0(b)-c/(a+c)*gamma_ratio(a)*zetaminus1(b)
               -c/(b+c)*gamma_ratio(b)*zetaminus1(a))


rays = [((1, 2, 3), 1), ((2, 3, 1), 4), ((3, 1, 2), -5)]
elementary = 6*sum(w*elementary_ray(*ray).coeff(t, 3) for ray, w in rays)
M = z01*z02-z03+g*zm2+(g*g-z2)*zm1-(g**3+g*z2)/12
Y = (zm3-z03)/3-(g**3-3*g*z2+2*z3)/18
result = s.factor(elementary-99*M-27*Y)
expected = 99*z01*z02+s.Rational(207, 2)*z03+s.Rational(162, 5)*zm3
assert s.expand(result-expected) == 0
assert sum(w*a*b*c for (a, b, c), w in rays) == 0
assert sum(w*c*(a*a+b*b-c*(a+b)) for (a, b, c), w in rays) == 0
# A changed coefficient must fail the claimed cancellation conditions.
assert sum(w*a*b*c for (a, b, c), w in [rays[0], rays[1], (rays[2][0], -4)]) != 0
report = {'exact_check_passed': True, 'result': str(result),
          'remainder_coefficient_M': -99, 'remainder_coefficient_Y': -27,
          'changed_coefficient_detected': True,
          'method': 'Direct Gamma/zeta series and two elementary restrictions'}
Path(__file__).resolve().parent.parent.joinpath("results", "independent_cubic_check.json").write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
