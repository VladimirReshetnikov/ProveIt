"""Independent rational check of the A321941 heat-kernel formula.

The first route uses BGG Lemma 14, coefficient extraction from B,C,D.
The second route builds tanh from its Riccati ODE and A from A'/A.
Only Python's standard library is used.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json

N = 64


def mul(a, b, degree=N):
    out = [F(0) for _ in range(degree + 1)]
    for i, ai in enumerate(a[:degree + 1]):
        if ai:
            for j, bj in enumerate(b[:degree + 1 - i]):
                if bj:
                    out[i + j] += ai * bj
    return out


# Independent first route: published BGG Lemma 14.
polynomials = ((1, (-6, 13, -7, 1)),
               (2, (6, -19, 17, -3)),
               (3, (-2, 11, -17, 6)))
d_bgg = [F(1)]
for k in range(1, N + 1):
    total = F(0)
    for j, dj in enumerate(d_bgg):
        power = k + 2 - j
        binomial = [F(1)]
        for m in range(1, power + 1):
            binomial.append(binomial[-1] * (F(2 * j + 1, 2) + m - 1) / m)
        factor = sum(F(coef) * s ** (power - l) * binomial[power - l]
                     for s, poly in polynomials
                     for l, coef in enumerate(poly) if l <= power)
        total += dj * factor
    d_bgg.append(-total / (8 * k))


# Independent second route: heat coefficients, no CAS power-series engine.
q = [F(0) for _ in range(N + 1)]
for m in range(N // 2 + 1):
    q[2 * m] = F(1, 4 ** m * factorial(2 * m + 1))
qi = [F(1)]
for n in range(1, N + 1):
    qi.append(-sum(q[j] * qi[n - j] for j in range(1, n + 1)))

# u'= (1-u^2)/4, u(0)=0 gives u=tanh(t/4).
u = [F(0)]
for n in range(1, N + 1):
    square = sum(u[j] * u[n - 1 - j] for j in range(n))
    u.append((int(n == 1) - square) / (4 * n))

log_derivative = []
for n in range(N):
    quotient = sum(j * q[j] * qi[n + 1 - j]
                   for j in range(1, n + 2))
    log_derivative.append(-quotient / 2 - (n + 1) * u[n + 1])
A = [F(1)]
for n in range(1, N + 1):
    A.append(sum(log_derivative[j] * A[n - 1 - j] for j in range(n)) / n)

b = [F(0), F(3, 16)]
for j in range(2, N + 1):
    b.append(b[-1] * F((2 * j - 3) * (2 * j + 1), 16 * j))
h = A.copy()
q_power = [F(1)] + [F(0)] * N
for j in range(1, N + 1):
    q_power = mul(q_power, q)
    term = mul(A, q_power, N - j)
    for k in range(j, N + 1):
        h[k] -= b[j] * term[k - j]

d_heat = []
rising_half = F(1)
for k in range(N + 1):
    d_heat.append(rising_half * h[k])
    rising_half *= F(2 * k + 1, 2)

assert d_heat == d_bgg, 'The two independent constructions disagree.'
assert all(d < 0 for d in d_bgg[3:])
assert d_bgg[:4] == [F(1), F(-7, 32), F(43, 2048), F(-915, 65536)]
assert b[16] > 100
assert b[16] > max(b[1:16])
assert b[15] > max(b[1:15])
assert all(b[j] > b[j-1] for j in range(6, N + 1))
assert F(3, 2) * 64 * F(6, 23) ** 32 < F(1, 100)
assert F(65, 64) ** 2 * F(6, 23) < 1
assert 24 * F(12, 23) ** 16 < F(1, 100)
assert F(33, 32) ** 2 * F(12, 23) < 1

result = {
    'method_1': 'BGG 2019 Lemma 14, direct coefficient extraction',
    'method_2': 'Riccati tanh and logarithmic-derivative heat coefficient construction',
    'agreement_through_degree': N,
    'negative_degree_range': [3, N],
    'first_seven_scaled_coefficients': [str(64 ** k * d_bgg[k]) for k in range(7)],
    'b_16': str(b[16]),
    'far_bound_k64_exact': str(F(3, 2) * 64 * F(6, 23) ** 32),
    'far_bound_k64_decimal': float(F(3, 2) * 64 * F(6, 23) ** 32),
    'improved_far_bound_k32_exact': str(24 * F(12, 23) ** 16),
    'improved_far_bound_k32_decimal': float(24 * F(12, 23) ** 16),
    'minimum_normalized_sign_margin_3_to_64': str(min(-h[k]/b[k] for k in range(3, N+1))),
    'd_coefficients': [str(x) for x in d_bgg],
}
target = Path(__file__).with_name('independent_check.json')
target.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k:v for k,v in result.items() if k != 'd_coefficients'}, indent=2))
