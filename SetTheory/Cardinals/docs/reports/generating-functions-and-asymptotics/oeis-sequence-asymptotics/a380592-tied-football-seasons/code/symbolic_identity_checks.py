#!/usr/bin/env python3
"""Independent symbolic leading-term identities in mean/difference coordinates."""
from output_support import write_result
import sympy as S
q, s, d, x, y, a, n = S.symbols('q s d x y a n')
weights = [(1 - q) / 2, (1 - q) / 2, q]
phases = [q * s + 3 * d, q * s - 3 * d, (q - 1) * s]
mu = {r: S.expand(sum((w * z ** r for w, z in zip(weights, phases)))) for r in range(2, 5)}
k4 = S.expand(mu[4] - 3 * mu[2] ** 2)
assert S.expand(k4 - (q * (1 - q) * (1 - 6 * q + 6 * q * q) * s ** 4 + 54 * q * (1 - q) * (2 * q - 1) * s * s * d * d + 81 * (1 - q) * (3 * q - 2) * d ** 4)) == 0
subs = {q: S.Rational(1, 3), s: (x + y) / 2, d: (x - y) / 2}
g3 = S.expand(mu[3].subs(subs) / 3)
G4 = S.expand(k4.subs(subs) / 12)
assert S.expand(G4 + (7 * x * x - 13 * x * y + 7 * y * y) ** 2 / 162) == 0
Y2, Y3, Y4 = S.symbols('Y2 Y3 Y4')
P = {0: n, 1: 0, 2: Y2, 3: Y3, 4: Y4}

def aggregate(poly):
    return S.expand(sum((c * (P[i] * P[j] - P[i + j]) / 2 for (i, j), c in S.Poly(S.expand(poly), x, y).terms())))
G3sum = aggregate(g3.subs({x: x + a, y: y + a}, simultaneous=True))
G4sum = aggregate(G4.subs({x: x + a, y: y + a}, simultaneous=True))
assert S.expand(G3sum - ((20 * n + 1) * Y3 / 81 + (13 * n + 1) * a * Y2 / 27 - n * (n - 1) * a ** 3 / 81)) == 0
assert S.expand(G4sum.subs(a, 0) + (98 * n - 1) * Y4 / 324 + S.Rational(89, 108) * Y2 ** 2) == 0
alpha = S.Rational(28, 9)
beta = S.Rational(2, 9)
quart = -S.Rational(98, 324) * 3 / alpha ** 2 - S.Rational(89, 108) / alpha ** 2
trans_var = S.Rational(20, 81) ** 2 * 6 / alpha ** 3
common_var = (S.Rational(13, 27) / alpha) ** 2 / beta
Klog = S.simplify(quart - (trans_var + common_var) / 2)
completed = S.simplify(Klog + S.Rational(9, 4) * S.Rational(13, 84) ** 2)
assert quart == -S.Rational(561, 3136)
assert trans_var == S.Rational(25, 2058)
assert common_var == S.Rational(169, 1568)
assert completed == -S.Rational(12181, 65856)
assert S.Rational(1, 28) + completed == -S.Rational(9829, 65856)
print('All symbolic checks passed')
print('Double-match quartic polynomial:', S.factor(G4))
print('Aggregated cubic without -i:', G3sum)
print('Aggregated quartic:', G4sum)
print('log K0:', Klog, '; after completing square:', completed)
write_result('symbolic_identity_checks', {'double_match_quartic': str(S.factor(G4)), 'aggregate_cubic': str(G3sum), 'aggregate_quartic': str(G4sum), 'quartic_mean': str(quart), 'transverse_cubic_variance': str(trans_var), 'common_cubic_variance': str(common_var), 'log_local_integral': str(Klog), 'completed_square_exponent': str(completed), 'leading_exponent': str(S.Rational(1, 28) + completed)})
