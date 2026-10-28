"""Independent rational arithmetic check of the degree-.51 schedule composition.

Imports no other script. The inherited recursive interfaces/flag lemma are
assumptions, not re-proved by this arithmetic check.
"""
import json
import sys
from fractions import Fraction as F
from math import isqrt
from pathlib import Path


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def root(x):
    D = 10 ** 40
    q = isqrt(x.numerator * D * D // x.denominator)
    lo, hi = F(q, D), F(q + 1, D)
    require(lo * lo <= x < hi * hi, 'square-root enclosure')
    return lo, hi


def atan_reciprocal(n):
    # Even-length alternating sum lies below atan(1/n).
    s = sum((F((-1) ** k, (2 * k + 1) * n ** (2 * k + 1)) for k in range(100)), F(0))
    return s, s + F(1, 201 * n ** 201)


def decimal_out(x, upward=False):
    D = 10 ** 24
    v = x.numerator * D // x.denominator
    if upward:
        v += 1
    return str(v // D) + '.' + str(v % D).zfill(24)


a, b = atan_reciprocal(2)
c, d = atan_reciprocal(3)
# atan(1/2)+atan(1/3)=pi/4, independently of the owner's Machin formula.
pi_lo, pi_hi = 4 * (a + c), 4 * (b + d)
ln_lo = 2 * sum((F(1, (2 * k + 1) * 3 ** (2 * k + 1)) for k in range(80)), F(0))
ln_hi = ln_lo + F(9, 4 * 161 * 3 ** 161)
two_lo, two_hi = root(F(2))
klo, khi = pi_lo * two_lo / ln_hi, pi_hi * two_hi / ln_lo
arities = [16, 16, 8, 6, 5, 4, 4]
budgets = [F(1531, 25000), F(1111, 10000), F(357, 2500), F(81, 500),
           F(1771, 10000), F(1911, 10000), F(1999, 10000)]
log_bounds = {16: F(4), 8: F(3), 6: F(517, 200), 5: F(1161, 500), 4: F(2), 3: F(317, 200)}
require(6 ** 200 < 2 ** 517 and 5 ** 500 < 2 ** 1161 and 3 ** 200 < 2 ** 317,
        'logarithm upper bounds')
mass, previous, low, high = F(1), F(0), F(0), F(0)
gates = []
for i, (r, total) in enumerate(zip(arities, budgets)):
    f = total - previous
    require(f > 0, 'positive taper')
    log_r = log_bounds[r]
    retained = F(51, 100) + (2 if i == 0 else 1) * total * log_r
    rounding = total * (1 + 2 * log_r)
    fresh = previous + 2 * total * log_r
    require(retained < 1 and rounding < 1 and fresh < 1, 'strict packing gates')
    b_squared = F((r - 1) * (4 * r + 10), 9 * r * r) if r in (4, 8, 16) else F({5: 18, 6: 24}[r], r * r)
    lo, hi = root(b_squared / f)
    low += mass * lo
    high += mass * hi
    gates.append({'r': r, 'mass': str(mass), 'taper': str(f),
                  'retained_slack': str(1 - retained), 'rounding_slack': str(1 - rounding),
                  'fresh_slack': str(1 - fresh)})
    mass *= F(2, r)
    previous = total
tail_f, tail_q = F(391, 40000), F(3, 4)
total_budget = previous + tail_f / (1 - tail_q)
require(mass == F(1, 7680) and total_budget == F(239, 1000), 'tail identities')
require(total_budget * (1 + 2 * log_bounds[3]) < 1, 'tail rounding')
require(F(51, 100) + total_budget * log_bounds[3] < 1, 'tail inherited degree')
require(total_budget < F(51, 100), 'new degree exponent')
require(F(2, 3) < F(7, 10) < tail_q, 'child/depth/taper bootstrap')
lo, hi = root(F(2, 3) / tail_f)
ql, qh = root(tail_q)
low += mass * lo / (1 - F(2, 3) / qh)
high += mass * hi / (1 - F(2, 3) / ql)
low *= klo
high *= khi
require(F(211394, 10000) < low < high < F(2114, 100), 'certified coefficient 21.14')
result = {'status': 'PASS', 'python_optimized': not __debug__,
          'scope': 'Independent schedule arithmetic/gates; inherited flag/recursion interfaces remain assumptions',
          'coefficient_interval': [decimal_out(low), decimal_out(high, True)],
          'safe_eventual_coefficient': '21.14', 'total_budget': str(total_budget), 'prefix_gates': gates,
          'leaf_threshold': 'ceil(s/ceil(log2 s))', 'root_degree_assumption': 'ceil(s^(51/100))'}
encoded = json.dumps(result, indent=2)
if len(sys.argv) > 1:
    Path(sys.argv[1]).write_text(encoded + '\n')
print(encoded)
