from repair_common import require, options, VerificationError
ARGS = options('Exact analytical certificate; repaired acceptance checks')
"""Independent cubic certificate for the later negative m=2 pressure coefficient."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json
N = 6
p = [F(0), F(-2), F(0), F(376, 45), F(6836, 189), F(105448, 2025), F(-35360872, 93555)]

def add(*polys):
    return [sum((v[i] if i < len(v) else 0 for v in polys)) for i in range(N + 1)]

def scale(v, c):
    return [c * x for x in v]

def mul(v, w):
    return [sum((v[j] * w[i - j] for j in range(i + 1))) for i in range(N + 1)]

def exp(v):
    q = [F(1)]
    for n in range(1, N + 1):
        q.append(sum((k * v[k] * q[n - k] for k in range(1, n + 1))) / n)
    return q
C = [F((-1) ** j * 2 ** (2 * j), factorial(2 * j)) for j in range(N + 1)]
rho = exp(p)
rho2 = mul(rho, rho)
rho3 = mul(rho, rho2)
res = add(rho3, scale(rho2, F(-3, 4)), scale(mul(C, rho2), -1), scale(rho, F(1, 4)), scale(mul(C, rho), F(5, 8)), [F(-1, 8)])
require(all((v == 0 for v in res)), 'Failed exact check: all((v == 0 for v in res))')
out = {'variable': 'u=t^2', 'pressure_coefficients_through_u6': list(map(str, p)), 'cubic': 'lambda^3-(3/4+C)lambda^2+(1/4+5C/8)lambda-1/8', 'C': 'cos(2t)', 'residual_through_u6': list(map(str, res)), 'simple_root_derivative_at_lambda1_C1': '3/8', 'coefficient_t12': '-35360872/93555', 'all_checks_passed': True}
(ARGS.output_dir / 'm2_negative_higher_certificate.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
