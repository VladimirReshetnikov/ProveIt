#!/usr/bin/env python3
"""Original exact checks for the adaptive-alphabet schedule; no archived code imported.
This is proof-supporting arithmetic, not an end-to-end tensor/SAT implementation.
"""
import sys

def demand(condition, message):
    """Fail closed in both normal and optimized Python execution."""
    if not condition:
        raise ArithmeticError(message)
from fractions import Fraction as F
from math import isqrt, log, log2, pi, sqrt
import json
from pathlib import Path
R = [13, 14, 8, 6, 5, 4, 4]
A = list(map(F, ['27/2000', '21/800', '333/10000', '1933/50000', '861/20000', '1183/25000', '4999/100000']))
X = [a - (A[d - 1] if d else F(0)) for d, a in enumerate(A)]
LIMIT = F(63, 1000)
B = LIMIT - A[-1]
THETA = F(3, 4)
M = [F(1)]
for r in R:
    M.append(M[-1] * F(2, r))
demand(X == list(map(F, ['27/2000', '51/4000', '141/20000', '67/12500', '439/100000', '427/100000', '267/100000'])), "certificate failed: X == list(map(F, ['27/2000', '51/4000', '141/20000', '67/12500', '439/100000', '427/100000', '267/100000']))")
demand(B == F(1301, 100000) and M[-1] == F(1, 5460), 'certificate failed: B == F(1301, 100000) and M[-1] == F(1, 5460)')
demand(all((x > 0 for x in X)) and F(2, 3) < F(7, 10) < THETA, 'certificate failed: all((x > 0 for x in X)) and F(2, 3) < F(7, 10) < THETA')
guards = []
for d, (r, a) in enumerate(zip(R, A)):
    c = (2 if d == 0 else 1) * a
    bound = F(1, 10) / c
    passed = pow(r, bound.denominator) < pow(2, bound.numerator)
    demand(passed, 'certificate failed: passed')
    guards.append({'depth': d, 'r': r, 'budget': str(a), 'exact_log_guard': f'{r}^{bound.denominator} < 2^{bound.numerator}', 'strict': passed, 'margin_display': 0.1 - float(c) * log2(r)})
bound = F(1, 10) / LIMIT
demand(pow(3, bound.denominator) < pow(2, bound.numerator), 'certificate failed: pow(3, bound.denominator) < pow(2, bound.numerator)')
guards.append({'depth': 'tail', 'r': 3, 'budget': str(LIMIT), 'exact_log_guard': f'3^{bound.denominator} < 2^{bound.numerator}', 'strict': True, 'margin_display': 0.1 - float(LIMIT) * log2(3)})
demand(2 * F(1, 10) + LIMIT == F(263, 1000) < 1, 'certificate failed: 2 * F(1, 10) + LIMIT == F(263, 1000) < 1')
demand(LIMIT < F(9, 10), 'certificate failed: LIMIT < F(9, 10)')
atan5_upper = sum(((-1) ** j * F(1, (2 * j + 1) * 5 ** (2 * j + 1)) for j in range(9)), F())
atan239_lower = F(1, 239) - F(1, 3 * 239 ** 3)
demand(16 * atan5_upper - 4 * atan239_lower < F(355, 113), 'certificate failed: 16 * atan5_upper - 4 * atan239_lower < F(355, 113)')
log2_lower = 2 * sum((F(1, (2 * j + 1) * 3 ** (2 * j + 1)) for j in range(4)), F())
demand(log2_lower > F(693, 1000), 'certificate failed: log2_lower > F(693, 1000)')
pi_over_ln2_upper = F(355, 113) / F(693, 1000)

def sqrt_upper(x, scale=10 ** 6):
    q = isqrt(x.numerator * scale * scale // x.denominator) + 1
    ans = F(q, scale)
    demand(ans * ans > x, 'certificate failed: ans * ans > x')
    return ans

def sqrt_lower(x, scale=10 ** 6):
    q = isqrt(x.numerator * scale * scale // x.denominator)
    ans = F(q, scale)
    demand(ans * ans <= x, 'certificate failed: ans * ans <= x')
    return ans
raw_terms = [M[d] * sqrt_upper(2 * (1 - F(1, r)) / X[d]) for d, r in enumerate(R)]
sqrt3_lower = sqrt_lower(F(3))
ratio_upper = F(4, 3) / sqrt3_lower
demand(ratio_upper < 1, 'certificate failed: ratio_upper < 1')
u7 = B * (1 - THETA)
tail_upper = M[-1] * sqrt_upper(F(4, 3) / u7) / (1 - ratio_upper)
constant_upper = pi_over_ln2_upper * (sum(raw_terms, F()) + tail_upper)
demand(constant_upper < 64, 'certificate failed: constant_upper < 64')
K = lambda r: pi * sqrt(2 * (1 - 1 / r)) / log(2)
level_values = [K(r) * float(M[d]) / sqrt(float(X[d])) for d, r in enumerate(R)]
tail_value = K(3) * float(M[-1]) / sqrt(float(u7)) / (1 - 2 / 3 / sqrt(float(THETA)))
constant_value = sum(level_values) + tail_value
baseline = pi / log(2) * (sqrt(150) + sqrt(50) / 3)
if '--negative-control=constant' in sys.argv:
    demand(constant_upper < 1, 'deliberate wrong constant bound rejected')
if '--negative-control=guard' in sys.argv:
    demand(13 ** 27 < 2 ** 99, 'deliberate wrong logarithm guard rejected')
out = {'status': 'PASS', 'scope': 'Exact schedule/guard/constant arithmetic only; not a SAT benchmark.', 'r': R, 'cumulative_budgets': [str(x) for x in A], 'retained_budgets': [str(x) for x in X], 'tail': {'r': 3, 'ratio': str(THETA), 'remaining_budget': str(B), 'total_budget': str(LIMIT), 'mass_at_start': str(M[-1])}, 'packing_guards': guards, 'secondary_exponent_upper': '263/1000', 'level_coefficient_displays': level_values, 'tail_coefficient_display': tail_value, 'coefficient_display': constant_value, 'certified_rational_upper': str(constant_upper), 'certified_upper_display': float(constant_upper), 'simple_certified_bound': 64, 'comparison_fixed16_slope4_boundary_display': baseline, 'coefficient_reduction_percent_display': 100 * (1 - constant_value / baseline), 'tail_uniform_taper_growth_exponent_display': 1 - log(4 / 3) / log(10 / 7)}
path = Path(next((arg.split('=',1)[1] for arg in sys.argv[1:] if arg.startswith('--output=')), str(Path(__file__).with_name('schedule_checks.json'))))
path.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
