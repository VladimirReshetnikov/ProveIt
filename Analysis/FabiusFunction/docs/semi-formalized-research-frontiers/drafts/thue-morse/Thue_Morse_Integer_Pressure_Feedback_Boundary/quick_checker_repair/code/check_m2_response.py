from repair_common import require, options, VerificationError
ARGS = options('Exact analytical certificate; repaired acceptance checks')
"""Exact normalized cubic certificate for H_(2,3)=-488/27."""
from fractions import Fraction as Q
from pathlib import Path
import json
N = 6

def add(*a):
    return [sum((p[k] if k < len(p) else Q(0) for p in a)) for k in range(N + 1)]

def scale(a, c):
    return [c * x for x in a]

def mul(a, b):
    return [sum((a[j] * b[k - j] for j in range(k + 1) if j < len(a) and k - j < len(b))) for k in range(N + 1)]

def power(a, n):
    v = [Q(1)]
    for _ in range(n):
        v = mul(v, a)
    return v
L = list(map(Q, [1, 0])) + [Q(1, 3), Q(8), Q(536, 27), -Q(488, 27), -Q(90472, 243)]
one = [Q(1), Q(1)]
res = add(scale(power(L, 3), 8), scale(mul(mul([Q(7), -Q(1)], one), power(L, 2)), -2), mul(mul([Q(7), -Q(3)], power(one, 3)), L), scale(power(one, 6), -1))
require(all((x == 0 for x in res)), 'Failed exact check: all((x == 0 for x in res))')
require(24 - 28 + 7 == 3, 'Failed exact check: 24 - 28 + 7 == 3')
out = {'all_checks_passed': True, 'normalized_eigenvalue_x_coefficients': list(map(str, L)), 'cubic_residual': list(map(str, res)), 'simple_root_derivative': 3, 'H_2_3': '-488/27'}
(ARGS.output_dir / 'm2_response_certificate.json').write_text(json.dumps(out, indent=2) + '\n')
print('Exact cubic confirms H_(2,3)=-488/27')
