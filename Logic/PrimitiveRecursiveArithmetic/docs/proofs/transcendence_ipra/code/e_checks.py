#!/usr/bin/env python3
"""Exact-arithmetic checks for the finite, prime-free Hermite argument for e.

All computations use integers and fractions.Fraction.  The program checks
finite polynomial identities, congruences for composite moduli, and three
concrete rational separation certificates.  It is NOT a formal proof of the
universal theorem and does not emit iPRA derivation certificates.

Run: python3 e_checks.py
No third-party dependencies are required.
"""

from fractions import Fraction as Q
from math import comb, factorial, gcd
import json


def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def add(a, b):
    c = [Q(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] += x
    for i, x in enumerate(b):
        c[i] += x
    return trim(c)


def scale(a, c):
    return trim([c * x for x in a])


def mul(a, b):
    if not a or not b:
        return []
    c = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    c[i + j] += x * y
    return trim(c)


def deriv(a):
    return trim([i * a[i] for i in range(1, len(a))])


def evaluate(a, x):
    v = Q(0)
    for coefficient in reversed(a):
        v = v * x + coefficient
    return v


def formal_integral(a, j):
    """The finite sum sum_k a[k] j^(k+1)/(k+1)."""
    v = Q(0)
    power = j
    for k, coefficient in enumerate(a):
        v += coefficient * Q(power, k + 1)
        power *= j
    return v


def coeff_norm(a, n):
    return sum((abs(c) * n**k for k, c in enumerate(a)), Q(0))


def exp_trunc(s, x):
    term = Q(1)
    value = term
    for r in range(1, s + 1):
        term *= Q(x, r)
        value += term
    return value


def exp_shift_poly(s, j):
    """Coefficient list for E_s(j-X)."""
    partial = [Q(1)]
    term = Q(1)
    for r in range(1, s + 1):
        term *= Q(j, r)
        partial.append(partial[-1] + term)
    return [(-1)**k * partial[s - k] / factorial(k) for k in range(s + 1)]


def shifted_power(s, j):
    return [Q(comb(s, k) * j**(s - k) * (-1)**k) for k in range(s + 1)]


def hermite_polynomials(n, p):
    """Return g, f, F with g=X^(p-1) product_(j=1)^n (X-j)^p."""
    g = [Q(0)] * (p - 1) + [Q(1)]
    for j in range(1, n + 1):
        factor = [Q(comb(p, k) * (-j)**(p - k)) for k in range(p + 1)]
        g = mul(g, factor)
    f = scale(g, Q(1, factorial(p - 1)))
    F = []
    current = f
    while current:
        F = add(F, current)
        current = deriv(current)
    return g, f, F


def theorem_parameters(coefficients):
    """The explicit primitive-recursive bounds in the accompanying proof.

    This is a transparent executable specification, not a practical numerical
    transcendence test. Even small inputs produce enormous cutoffs.
    """
    coefficients = trim(coefficients)
    if not coefficients:
        raise ValueError("The zero polynomial has no separation bound.")
    r = next(i for i, x in enumerate(coefficients) if x != 0)
    a = coefficients[r:]
    n = len(a) - 1
    if n == 0:
        return {"r": r, "n": n, "D": 1, "N": 0}
    S = sum(abs(x) for x in a)
    C = (2 * n)**(n + 1)
    A = n * 3**(2 * n) * S
    M = abs(a[0]) * factorial(n)
    B = 4 * C * C + 4 * A * C + 1
    q = M * B
    p = 2 * q + 1
    d = (n + 1) * p - 1
    D = factorial(d) * factorial(n + 1)**p
    H = (d + 1) * D * n**d
    R = 2 * n
    W = S * n * (H + 2 * D)
    t = 4 * R * R + 4 * W + 1
    N = 2 * t
    return dict(r=r, n=n, S=S, C=C, A=A, M=M, B=B, q=q, p=p,
                d=d, D=D, H=H, R=R, W=W, t=t, N=N)


def check_exp_lemmas():
    count = 0
    for s in range(0, 15):
        e = exp_trunc(s, 1)
        assert 1 <= e < 3
        for j in range(0, 7):
            assert exp_trunc(s, j) <= e**j <= 3**j
            difference = e**j - exp_trunc(s, j)
            assert difference >= 0
            if j and s + 2 >= 2 * j:
                assert difference <= Q(2 * j**(s + 1), factorial(s + 1))
            count += 1
        for v in range(s, s + 5):
            if s >= 1:
                assert 0 <= exp_trunc(v, 1) - e <= Q(2, factorial(s + 1))
    return count


def check_example(a, p=25, s=128):
    n = len(a) - 1
    assert n >= 1 and a[0] and gcd(p, abs(a[0]) * factorial(n)) == 1
    # Deliberately use a composite modulus in all displayed examples.
    assert any(p % k == 0 for k in range(2, p))
    g, f, F = hermite_polynomials(n, p)
    d = (n + 1) * p - 1
    assert len(g) - 1 == d
    assert add(F, scale(deriv(F), -1)) == f

    values = [evaluate(F, j) for j in range(n + 1)]
    assert all(x.denominator == 1 for x in values)
    assert all(values[j].numerator % p == 0 for j in range(1, n + 1))
    residue = (-1)**(n * p) * factorial(n)**p
    assert (values[0].numerator - residue) % p == 0
    T = sum(a[j] * values[j] for j in range(n + 1))
    assert T.denominator == 1 and T != 0
    assert (T.numerator - a[0] * residue) % p == 0

    D = factorial(d) * factorial(n + 1)**p
    H = (d + 1) * D * n**d
    assert abs(values[0]) <= D
    assert coeff_norm(F, n) <= H

    e = exp_trunc(s, 1)
    sum_J = Q(0)
    sum_K = Q(0)
    discrepancy = Q(0)
    for j in range(n + 1):
        shifted_exp = exp_shift_poly(s, j)
        shifted_F = mul(scale(shifted_power(s, j), Q(1, factorial(s))), F)
        J = formal_integral(mul(shifted_exp, f), j)
        K = formal_integral(shifted_F, j)
        assert values[0] * exp_trunc(s, j) - values[j] == J - K
        assert abs(J) <= n * coeff_norm(shifted_exp, n) * coeff_norm(f, n)
        assert coeff_norm(shifted_exp, n) <= exp_trunc(s, j + n)
        assert abs(K) <= Q(n * H * (2 * n)**s, factorial(s))
        sum_J += a[j] * J
        sum_K += a[j] * K
        discrepancy += a[j] * (e**j - exp_trunc(s, j))

    correction = values[0] * discrepancy
    error = sum_J - sum_K + correction
    actual = evaluate(a, e)
    assert values[0] * actual == T + error

    # These are concrete exact rational certificates at s=128, independently
    # of the much larger uniform bounds of the general theorem.
    assert abs(sum_J) < Q(1, 4)
    assert abs(sum_K) + abs(correction) < Q(1, 4)
    assert abs(error) < Q(1, 2)
    assert abs(values[0] * actual) > Q(1, 2)
    assert 2 * D * abs(actual) > 1
    return {
        "coefficients_low_to_high": a,
        "composite_modulus": p,
        "hermite_degree": d,
        "exp_truncation": s,
        "integral_identity": "exact",
        "nonzero_integer_congruence": "passed",
        "rational_separation_certificate": "passed",
        "evaluation_sign": 1 if actual > 0 else -1,
    }


def main():
    exp_cases = check_exp_lemmas()
    examples = [check_example(a) for a in ([-2, 1], [1, -3, 2], [-2, 0, 0, 1])]
    parameters = theorem_parameters([-2, 1])
    # Output bit lengths, avoiding an impractical decimal expansion of N.
    summary = {
        "status": "all exact checks passed",
        "scope": "finite arithmetic checks, not a formal universal iPRA proof",
        "finite_exponential_cases": exp_cases,
        "examples": examples,
        "general_bound_example": {
            "coefficients_low_to_high": [-2, 1],
            "p": parameters["p"],
            "d": parameters["d"],
            "D_bit_length": parameters["D"].bit_length(),
            "N_bit_length": parameters["N"].bit_length(),
        },
    }
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
