"""Exact-arithmetic recurrence control derived from the existing verifier.

The earlier joint-Cauchy packet's verify_joint_cauchy_independent.py already
uses a quadratic-number-of-operations rational recurrence. This reference
adapts it to both Q and Q(U), removes verification from timed sections, and
adds the same safe mode cutoff used by the new modular implementation.
It is a strengthened reference control, not a claimed new algorithm.
"""
from fractions import Fraction
from reference_joint_cauchy import exact_divide, power_of_two


def feature_tables(kernel, precision, truncate=True):
    n = kernel.size
    B = next((b for b in range(n) if kernel.weight(b) >= precision), n) if truncate else n
    target = [[Fraction(0)]*n for _ in range(B)]
    source = [[Fraction(0)]*n for _ in range(B)]
    prefactor = kernel.prefactor()
    T = kernel.T
    slots = [kernel.slot(j) for j in range(n)]
    for j, x in enumerate(slots):
        P = Q = Fraction(1)
        for b in range(min(B, j+1)):
            d = x-slots[b]
            e = kernel.E(b)
            target[b][j] = exact_divide(prefactor * power_of_two(e) * T * P, T+d)
            source[b][j] = exact_divide(T*Q, power_of_two(e)*(T-d))
            if d:
                P = exact_divide(P*d, T+d)
                Q = exact_divide(-Q*d, T-d)
    return target, source
