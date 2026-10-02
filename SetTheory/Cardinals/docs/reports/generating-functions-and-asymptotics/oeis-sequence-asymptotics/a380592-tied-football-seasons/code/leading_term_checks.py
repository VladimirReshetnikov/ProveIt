#!/usr/bin/env python3
"""Exact leading-term identities, small counts, and numerical diagnostics.

Counts for n=1,...,4 are recomputed by score-vector dynamic programming.
The n=5,...,8 entries are reference inputs used only in the diagnostic table.
These small-n ratios are not evidence establishing the asymptotic theorem.
"""
import json, math
from collections import defaultdict
from output_support import write_result
import sympy as s
out = {}
x, y, q = s.symbols('x y q')
p = (1 - q) / 2
mu = (3 - q) * (x + y) / 2
vals = [3 * x - mu, x + y - mu, 3 * y - mu]
probs = [p, q, p]
mom = lambda r: s.expand(sum((w * v ** r for w, v in zip(probs, vals))))
k2 = mom(2)
k3 = mom(3)
k4 = s.expand(mom(4) - 3 * k2 ** 2)
S, D = s.symbols('S D')
assert s.factor(k4.subs({x: S + D, y: S - D}, simultaneous=True)) == s.factor(q * (1 - q) * (1 - 6 * q + 6 * q * q) * S ** 4 + 54 * q * (1 - q) * (2 * q - 1) * S * S * D * D + 81 * (1 - q) * (3 * q - 2) * D ** 4)
assert s.expand(k3.subs({x: S + D, y: S - D, q: s.Rational(1, 3)}, simultaneous=True)) == s.expand(-s.Rational(2, 27) * S ** 3 + 6 * S * D * D)
k30 = s.expand(k3.subs(q, s.Rational(1, 3)))
k40 = s.expand(k4.subs(q, s.Rational(1, 3)))
out['single_match_cumulants_q_one_third'] = {'kappa2': str(s.expand(k2.subs(q, s.Rational(1, 3)))), 'kappa3': str(k30), 'kappa4': str(k40)}
# Deterministic rational test families include nonzero common means.
for n in range(3, 18):
    for seed in range(1, 10):
        yy = [s.Rational((i * i + seed * i + seed ** 2) % 17 - 8) for i in range(n - 1)]
        yy.append(-sum(yy))
        a = s.Rational(seed - 5, 7)
        v = [z + a for z in yy]
        Y2 = sum((z * z for z in yy))
        Y3 = sum((z ** 3 for z in yy))
        Y4 = sum((z ** 4 for z in yy))
        c3 = sum((k30.subs({x: v[i], y: v[j]}) for i in range(n) for j in range(i + 1, n)))
        assert s.simplify(c3 / 3 - ((20 * n + 1) * Y3 / s.Integer(81) + (13 * n + 1) * a * Y2 / s.Integer(27) - n * (n - 1) * a ** 3 / s.Integer(81))) == 0
        c4 = sum((k40.subs({x: yy[i], y: yy[j]}) for i in range(n) for j in range(i + 1, n)))
        assert s.simplify(c4 / 12 + (98 * n - 1) * Y4 / s.Integer(324) + s.Rational(89, 108) * Y2 ** 2) == 0
out['symmetric_polynomial_checks'] = 15 * 9
alpha = s.Rational(28, 9)
beta = s.Rational(2, 9)
quartic = -s.Rational(98, 324) * 3 / alpha ** 2 - s.Rational(89, 108) / alpha ** 2
transverse_var = s.Rational(20, 81) ** 2 * 6 / alpha ** 3
shift = s.Rational(13, 84)
common_exponent = -shift ** 2 / (2 * beta)
exact_exponent = quartic - transverse_var / 2
asym_exponent = exact_exponent + s.Rational(1, 28)
assert quartic == -s.Rational(561, 3136)
assert transverse_var == s.Rational(25, 2058)
assert common_exponent == -s.Rational(169, 3136)
assert exact_exponent == -s.Rational(12181, 65856)
assert asym_exponent == -s.Rational(9829, 65856)
out['constants'] = {k: str(v) for k, v in locals().copy().items() if k in ('quartic', 'transverse_var', 'shift', 'common_exponent', 'exact_exponent', 'asym_exponent')}
# Enumerate every score vector for two distinguished games per pair.
small = []
for n in range(1, 5):
    state = {(0,) * n: 1}
    for i in range(n):
        for j in range(i + 1, n):
            for game in range(2):
                nxt = defaultdict(int)
                for scores, count in state.items():
                    for u, v in [(3, 0), (1, 1), (0, 3)]:
                        z = list(scores)
                        z[i] += u
                        z[j] += v
                        nxt[tuple(z)] += count
                state = nxt
    count = sum((v for scores, v in state.items() if len(set(scores)) == 1))
    small.append(count)
assert small == [1, 3, 27, 1083]
out['exact_counts_n1_to4'] = small
exact = [1, 3, 27, 1083, 296081, 696779523, 16503494334993, 3439079361325736243]
checks = []
for n, count in enumerate(exact, 1):
    c = 8 * (n - 1) / 3 - float(shift)
    # Truncation at |j| <= 4 has the tail bound exported below.
    theta = sum((math.exp(-4 * math.pi ** 2 * j * j / 9) * math.cos(2 * math.pi * j * c) for j in range(-4, 5)))
    logmain = n * (n - 1) * math.log(3) - math.log(n) / 2 + (n - 1) / 2 * math.log(9 / (56 * math.pi * n)) + float(asym_exponent) + math.log(theta)
    checks.append({'n': n, 'exact': count, 'theta': theta, 'leading_approximation': math.exp(logmain), 'exact_over_leading': count / math.exp(logmain)})
out['small_n_diagnostic_only'] = checks
out['theta_truncation_absolute_error_bound'] = 2 * math.exp(-4 * math.pi ** 2 * 25 / 9) / (1 - math.exp(-4 * math.pi ** 2 * 11 / 9))
write_result('leading_term_checks', out)
print(json.dumps(out, indent=2))
