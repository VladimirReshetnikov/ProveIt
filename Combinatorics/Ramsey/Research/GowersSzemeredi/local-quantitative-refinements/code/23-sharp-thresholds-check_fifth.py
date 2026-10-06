#!/usr/bin/env python3
"""Exact finite certificates for the characteristic-five cube section.

No third-party packages are required. Polynomial coefficients are integers.
The main proof is in gowers_sharp_thresholds.tex; these checks validate its finite
expansions, not the dimension-free analytic inequalities.
"""

from collections import Counter
from itertools import product


def add(*polys):
    answer = Counter()
    for poly in polys:
        for monomial, coefficient in poly.items():
            answer[monomial] += coefficient
    return {m: c for m, c in answer.items() if c}


def scale(poly, coefficient):
    return {m: c * coefficient for m, c in poly.items() if c * coefficient}


def monomial(exponents, coefficient=1):
    return {tuple(exponents): coefficient}


def multiply(p, q):
    answer = Counter()
    for m, c in p.items():
        for n, d in q.items():
            answer[tuple(x + y for x, y in zip(m, n))] += c * d
    return {m: c for m, c in answer.items() if c}


def multiply_all(*polys):
    answer = monomial((0,) * len(next(iter(polys[0])))) if polys[0] else {}
    for poly in polys:
        answer = multiply(answer, poly)
    return answer


def power(p, n):
    assert n >= 1
    answer = p
    for _ in range(n - 1):
        answer = multiply(answer, p)
    return answer


def conjugate(p):
    # Formal variables are delta, a_1, bar(a_1), a_2, bar(a_2).
    return {(m[0], m[2], m[1], m[4], m[3]): c for m, c in p.items()}


unit_vectors = [tuple(int(i == j) for i in range(5)) for j in range(5)]
delta, a1, a4, a2, a3 = [monomial(v) for v in unit_vectors]
a = [{}, a1, a2, a3, a4]
w = [delta, a1, a2, a3, a4]


def slot(coefficients, s, t):
    return add(*(multiply_all(coefficients[r],
                              conjugate(coefficients[(r + s) % 5]),
                              conjugate(coefficients[(r + t) % 5]),
                              coefficients[(r + s + t) % 5])
                 for r in range(5)))


def cube(coefficients):
    return add(*(multiply(slot(coefficients, s, t),
                          conjugate(slot(coefficients, s, t)))
                 for s, t in product(range(5), repeat=2)))


lam = [multiply(x, conjugate(x)) for x in a]
S = add(*(power(x, 2) for x in lam))
B5 = add(*(multiply_all(a[2 * r % 5], power(a[-r], 3), a[r])
           for r in range(5)))
A6 = add(*(multiply_all(lam[s], lam[t], lam[(s + t) % 5])
           for s, t in product(range(5), repeat=2)))
B6 = add(*(multiply_all(power(a[t], 2), lam[(s + t) % 5],
                       a[s], conjugate(a[(s + 2 * t) % 5]))
           for s, t in product(range(5), repeat=2)))
C6 = add(*(multiply_all(power(a[s], 2), power(a[t], 2),
                       power(conjugate(a[(s + t) % 5]), 2))
           for s, t in product(range(5), repeat=2)))
full = cube(w)


def coefficient_in_delta(poly, degree):
    return {(0,) + m[1:]: c for m, c in poly.items() if m[0] == degree}


assert coefficient_in_delta(full, 8) == monomial((0,) * 5)
for degree in (7, 6, 5):
    assert coefficient_in_delta(full, degree) == {}
assert coefficient_in_delta(full, 4) == scale(S, 12)
assert coefficient_in_delta(full, 3) == scale(B5, 8)
assert coefficient_in_delta(full, 2) == add(scale(A6, 12), scale(B6, 12),
                                         scale(C6, 4))
assert coefficient_in_delta(full, 0) == cube(a)
print("PASS: exact centered cube expansion through degree six on Z/5.")


def selected_phase(poly):
    """Substitute a1=rho*z, a2=b*z^2, z^10=-1 exactly.

    Output monomials are delta, rho, b, z. The identity is valid at
    z=exp(i*pi/10), with no floating-point approximation.
    """
    answer = Counter()
    for (d, x, xc, y, yc), c in poly.items():
        exponent = x - xc + 2 * (y - yc)
        quotient, remainder = divmod(exponent, 10)
        sign = -1 if quotient % 2 else 1
        answer[(d, x + xc, y + yc, remainder)] += c * sign
    return {m: c for m, c in answer.items() if c}


def simple(*terms):
    return {(d, r, b, 0): coefficient for d, r, b, coefficient in terms}


table = {
    (0, 0): simple((4, 0, 0, 1), (0, 4, 0, 2), (0, 0, 4, 2)),
    (0, 1): simple((2, 2, 0, 2), (0, 2, 2, 2), (0, 0, 4, 1)),
    (0, 2): simple((2, 0, 2, 2), (0, 2, 2, 2), (0, 4, 0, 1)),
    (1, 1): simple((2, 2, 0, 1), (1, 2, 1, 2)),
    (2, 2): simple((2, 0, 2, 1)),
    (1, 2): simple((0, 2, 2, 1), (1, 2, 1, 2)),
}
for (s, t), expected in table.items():
    assert selected_phase(slot(w, s, t)) == expected
print("PASS: all six exact Fourier-slot table entries.")

expected_norm = simple((0, 8, 0, 8), (0, 6, 2, 16), (0, 4, 4, 48),
                       (0, 2, 6, 16), (0, 0, 8, 8))
expected_full = add(expected_norm,
                    simple((8, 0, 0, 1), (4, 4, 0, 24), (4, 0, 4, 24),
                           (3, 4, 1, 16), (2, 4, 2, 96), (2, 2, 4, 48),
                           (1, 4, 3, 32)))
assert selected_phase(cube(a)) == expected_norm
assert selected_phase(full) == expected_full
print("PASS: exact centered norm and complete five-point model polynomial.")

vertices = list(product(range(2), repeat=3))
distance_counts = Counter(sum(x != y for x, y in zip(v, w))
                          for i, v in enumerate(vertices)
                          for w in vertices[i + 1:])
assert distance_counts == {1: 12, 2: 12, 3: 4}
print("PASS: six-vertex support multiplicities 12, 12, 4.")
print("All exact characteristic-five certificates passed.")
