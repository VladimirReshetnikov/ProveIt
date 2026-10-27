#!/usr/bin/env python3
"""Original exact arithmetic certificate for the gamma=51/100 specialization.
No archived source code is imported or executed. Not a SAT implementation.
"""
import sys

def demand(condition, message):
    """Fail closed in both normal and optimized Python execution."""
    if not condition:
        raise ArithmeticError(message)
from fractions import Fraction as F
from math import isqrt, log, log2, pi, sqrt
from pathlib import Path
import json
R = [15, 15, 8, 6, 5, 4, 4]
A = [F(v) for v in ['627/10000', '2269/20000', '357/2500', '81/500', '1771/10000', '1911/10000', '1999/10000']]
X = [a - (A[d - 1] if d else 0) for d, a in enumerate(A)]
GAMMA = F(51, 100)
LIMIT = F(239, 1000)
THETA = F(3, 4)
B = LIMIT - A[-1]
demand(B == F(391, 10000), 'certificate failed: B == F(391, 10000)')
M = [F(1)]
for r in R:
    M.append(M[-1] * F(2, r))
demand(M[-1] == F(1, 6750) and LIMIT < GAMMA, 'certificate failed: M[-1] == F(1, 6750) and LIMIT < GAMMA')

def log_guard(r, bound):
    demand(r ** bound.denominator < 2 ** bound.numerator, 'certificate failed: r ** bound.denominator < 2 ** bound.numerator')
    return f'{r}^{bound.denominator} < 2^{bound.numerator}'
rows = []
for d, (r, a) in enumerate(zip(R, A)):
    factor = 2 if d == 0 else 1
    main = log_guard(r, (1 - GAMMA) / (factor * a))
    rounding = log_guard(r, (1 - a) / (2 * a))
    rows.append({'depth': d, 'r': r, 'A': str(a), 'x': str(X[d]), 'degree_guard': main, 'rounding_guard': rounding, 'degree_exponent_display': float(GAMMA) + factor * float(a) * log2(r), 'rounding_exponent_display': float(a) * (1 + 2 * log2(r))})
rows.append({'depth': 'tail', 'r': 3, 'A': str(LIMIT), 'degree_guard': log_guard(3, (1 - GAMMA) / LIMIT), 'rounding_guard': log_guard(3, (1 - LIMIT) / (2 * LIMIT)), 'degree_exponent_display': float(GAMMA) + float(LIMIT) * log2(3), 'rounding_exponent_display': float(LIMIT) * (1 + 2 * log2(3))})

def su(x, S=10 ** 6):
    q = isqrt(x.numerator * S * S // x.denominator) + 1
    v = F(q, S)
    demand(v * v > x, 'certificate failed: v * v > x')
    return v
S = 10 ** 6
sqrt3lower = F(isqrt(3 * S * S), S)
demand(sqrt3lower ** 2 < 3, 'certificate failed: sqrt3lower ** 2 < 3')
ratio_upper = F(4, 3) / sqrt3lower
raw = sum((M[d] * su(2 * (1 - F(1, r)) / X[d]) for d, r in enumerate(R)), F())
raw += M[-1] * su(F(4, 3) / (B / 4)) / (1 - ratio_upper)
atan5up = sum(((-1) ** j * F(1, (2 * j + 1) * 5 ** (2 * j + 1)) for j in range(9)), F())
atan239low = F(1, 239) - F(1, 3 * 239 ** 3)
demand(16 * atan5up - 4 * atan239low < F(355, 113), 'certificate failed: 16 * atan5up - 4 * atan239low < F(355, 113)')
demand(2 * sum((F(1, (2 * j + 1) * 3 ** (2 * j + 1)) for j in range(4)), F()) > F(693, 1000), 'certificate failed: 2 * sum((F(1, (2 * j + 1) * 3 ** (2 * j + 1)) for j in range(4)), F()) > F(693, 1000)')
upper = F(355, 113) / F(693, 1000) * raw
demand(upper < 30, 'certificate failed: upper < 30')
K = lambda r: pi * sqrt(2 * (1 - 1 / r)) / log(2)
vals = [K(r) * float(M[d]) / sqrt(float(X[d])) for d, r in enumerate(R)]
tail = K(3) * float(M[-1]) / sqrt(float(B / 4)) / (1 - 2 / 3 / sqrt(0.75))
if '--negative-control=constant' in sys.argv:
    demand(upper < 1, 'deliberate wrong constant bound rejected')
if '--negative-control=guard' in sys.argv:
    demand(13 ** 27 < 2 ** 99, 'deliberate wrong logarithm guard rejected')
out = {'status': 'PASS', 'scope': 'Exact arithmetic only; gamma=51/100 normalized contraction specialization.', 'gamma': str(GAMMA), 'finite_alphabets': R, 'cumulative_budgets': [str(v) for v in A], 'retained_budgets': [str(v) for v in X], 'tail': {'r': 3, 'ratio': str(THETA), 'total_budget': str(LIMIT), 'remaining_budget': str(B), 'mass': str(M[-1])}, 'guards': rows, 'finite_coefficient_displays': vals, 'tail_coefficient_display': tail, 'coefficient_display': sum(vals) + tail, 'certified_rational_upper': str(upper), 'certified_upper_display': float(upper), 'simple_eventual_coefficient': 30, 'new_packet_degree_exponent_limit': str(LIMIT)}
Path(next((a.split('=',1)[1] for a in sys.argv[1:] if a.startswith('--output=')), str(Path(__file__).with_name('degree_51_schedule_checks.json')))).write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
