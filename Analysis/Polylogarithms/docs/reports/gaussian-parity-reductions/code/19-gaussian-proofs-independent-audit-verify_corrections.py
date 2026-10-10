"""Independent numerical sign checks; the accompanying TeX supplies proofs."""
import argparse
import json
from pathlib import Path
from fractions import Fraction
from math import comb
import mpmath as mp

mp.mp.dps = 90


def display(value):
    return mp.nstr(value, 82)


def li11(x, y):
    # Independent one-dimensional integral from the defining derivative.
    return mp.quad(lambda t: -x * mp.log(1 - x*y*t)/(1 - x*t), [0, 1])


def exact_radius_checks():
    tested = 0
    for w in range(1, 33):
        ceil_log = w.bit_length()
        for p in [0, 1, 8, 30, 100]:
            n = 3*(p+w+ceil_log)
            radius = Fraction(2*(w+1)*sum(comb(n, k) for k in range(w)), 2**n)
            assert radius <= Fraction(1, 2**p)
            tested += 1
    return tested


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--exact-only',action='store_true')
parser.add_argument('--output',type=Path,default=
    Path(__file__).resolve().parents[3]/'results'/'independent'/'audit'/'correction_checks.json')
args = parser.parse_args()
args.output.parent.mkdir(parents=True,exist_ok=True)
if args.exact_only:
    tested_radius_cases = exact_radius_checks()
    args.output.write_text(json.dumps({
        'status':'Exact rational truncation-bound checks only.',
        'exact_uniform_radius_checks':tested_radius_cases},indent=2)+'\n')
    print(f'All {tested_radius_cases} exact rational radius checks passed.')
    raise SystemExit(0)


lhs = mp.im(li11(-1, 1j) - li11(1j, -1))
rhs = mp.pi*mp.log(2)/2 - mp.catalan
positive_integral = mp.quad(lambda t: mp.log(1+t*t)/(1+t*t), [0, 1])

diag_formula = (9*mp.zeta(3)**2/2048 + 47*mp.pi**6/1935360
                -3j*mp.pi**3*mp.zeta(3)/1024)
diag_stuffle = (mp.polylog(3, 1j)**2 - mp.polylog(6, -1))/2

component_rows = []
for c in [mp.mpf(1)/3, mp.mpf(1)/2, mp.mpf(2)/3]:
    for m in range(5):
        t = mp.mpf('0.37')
        z = (1-c)/2 + 1j*t
        evaluated = mp.re(1j**m*(mp.polygamma(m, z+c)-mp.polygamma(m, z)))
        f = lambda y: mp.pi*mp.sin(mp.pi*c)/(mp.cosh(2*mp.pi*y)+mp.cos(mp.pi*c))
        target = mp.diff(f, t, m)
        assert abs(evaluated-target) < mp.mpf('1e-80')
        component_rows.append({'c': display(c), 'm': m,
                               'residual': display(evaluated-target)})

# Exact checks of the explicit, uniform truncation prescription.
tested_radius_cases = exact_radius_checks()

out = {
    'precision_decimal_digits': mp.mp.dps,
    'status': 'Numerical checks only, except the rational truncation-bound cases.',
    'mixed_diagonal_antisymmetry': {
        'integral_difference': display(lhs), 'closed_form': display(rhs),
        'positive_integral': display(positive_integral),
        'residual': display(lhs-rhs)},
    'Li33_diagonal': {'real': display(mp.re(diag_formula)),
                      'imag': display(mp.im(diag_formula)),
                      'residual_modulus': display(abs(diag_formula-diag_stuffle))},
    'digamma_component_checks': component_rows,
    'exact_uniform_radius_checks': tested_radius_cases,
}
assert abs(lhs-rhs) < mp.mpf('1e-80')
assert abs(positive_integral-rhs) < mp.mpf('1e-80')
assert abs(diag_formula-diag_stuffle) < mp.mpf('1e-80')
path = args.output
path.write_text(json.dumps(out, indent=2) + '\n')
print(f'Wrote {path}; all 15 component checks and 160 exact radius checks passed.')
