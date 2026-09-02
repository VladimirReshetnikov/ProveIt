#!/usr/bin/env python3
"""Exact experiments for dyadic extrapolation of Rvachev up-splines.

The user-indexed approximant ``up_n`` is the inverse Fourier transform of

    product_{k=0}^n sinc(pi*t/2^k).

Thus it is the convolution of n+1 centered uniform densities.  Every
calculation below uses fractions.Fraction; no floating-point arithmetic is
used in the mathematical verification.

Main checks
-----------
1. Evaluate up_n(x) from the exact Thue--Morse truncated-power formula.
2. For x of reduced dyadic depth d, put M=floor(d/2) and Q=1/4.
3. Recover up(x) from q_n,...,q_{n+M} using the closed q-Pochhammer weights.
4. Recover every geometric-mode coefficient by solving the exact
   q-Vandermonde system.
5. Verify the predicted formula at additional, unused values of n.
6. Verify the finite q-binomial annihilating recurrence.

The direct truncated-power evaluator has exponential cost in n.  It is meant
as a transparent proof-of-concept and regression test, not as the fastest
possible evaluator for very deep dyadic points.
"""

from __future__ import annotations

from fractions import Fraction
from math import factorial
from typing import Iterable, List, Sequence, Tuple

Q = Fraction(1, 4)


def thue_morse_sign(k: int) -> int:
    """Return tau_k=(-1)^(binary digit sum of k)."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    return -1 if k.bit_count() & 1 else 1


def is_power_of_two(n: int) -> bool:
    return n > 0 and (n & (n - 1)) == 0


def dyadic_depth(x: Fraction) -> int:
    """Smallest d>=0 such that 2^d*x is an integer.

    Fraction automatically reduces x, so for a nonintegral dyadic number the
    denominator is exactly 2^d.
    """
    if not is_power_of_two(x.denominator):
        raise ValueError(f"{x} is not dyadic")
    return x.denominator.bit_length() - 1


def finite_up(n: int, x: Fraction) -> Fraction:
    r"""Evaluate the finite-product spline up_n(x) exactly.

    With N=n+1 factors, the exact truncated-power formula is

      up_n(x) = 2^(n(n+1)/2)/n! * sum_{k=0}^{2^(n+1)-1}
                tau_k * (x + 1 - 2^(-(n+1)) - k/2^n)_+^n.

    For n=0, y_+^0 is interpreted as 1 for y>0 and 0 for y<=0.
    The dyadic points used after the theorem's threshold are never knots, so
    the convention at y=0 has no effect on the reported experiments.
    """
    if n < 0:
        raise ValueError("n must be nonnegative")
    if not isinstance(x, Fraction):
        x = Fraction(x)

    scale = 1 << n
    delta = Fraction(1, 1 << (n + 1))
    shifted_x = x + 1 - delta
    total = Fraction(0)

    # Terms are positive only while k/2^n < shifted_x.  We retain the simple
    # exact test rather than introducing a floor convention at knots.
    for k in range(1 << (n + 1)):
        y = shifted_x - Fraction(k, scale)
        if y > 0:
            total += thue_morse_sign(k) * (y ** n)

    prefactor = Fraction(1 << (n * (n + 1) // 2), factorial(n))
    return prefactor * total


def q_pochhammer(q: Fraction, length: int) -> Fraction:
    """Return (q;q)_length = product_{r=1}^length (1-q^r)."""
    if length < 0:
        raise ValueError("length must be nonnegative")
    ans = Fraction(1)
    for r in range(1, length + 1):
        ans *= 1 - q**r
    return ans


def gaussian_binomial(n: int, k: int, q: Fraction = Q) -> Fraction:
    """Return the Gaussian binomial [n choose k]_q as an exact fraction."""
    if k < 0 or k > n:
        return Fraction(0)
    return q_pochhammer(q, n) / (
        q_pochhammer(q, k) * q_pochhammer(q, n - k)
    )


def extraction_weights(M: int, q: Fraction = Q) -> List[Fraction]:
    r"""Weights extracting the constant term from geometric samples.

    If y_j=P(q^j), j=0,...,M, for a polynomial P of degree <=M, then

      P(0) = sum_j w_j y_j,

    where

      w_j = (-1)^(M-j) q^((M-j+1)(M-j)/2)
            / ((q;q)_j (q;q)_(M-j)).
    """
    if M < 0:
        raise ValueError("M must be nonnegative")
    weights: List[Fraction] = []
    for j in range(M + 1):
        exponent = (M - j + 1) * (M - j) // 2
        numerator = ((-1) ** (M - j)) * q**exponent
        denominator = q_pochhammer(q, j) * q_pochhammer(q, M - j)
        weights.append(numerator / denominator)
    return weights


def extract_limit(samples: Sequence[Fraction], q: Fraction = Q) -> Fraction:
    """Apply the q-Pochhammer extrapolation formula to M+1 samples."""
    if not samples:
        raise ValueError("at least one sample is required")
    weights = extraction_weights(len(samples) - 1, q)
    return sum((w * y for w, y in zip(weights, samples)), Fraction(0))


def solve_fraction_system(
    matrix: Sequence[Sequence[Fraction]], rhs: Sequence[Fraction]
) -> List[Fraction]:
    """Solve a square nonsingular linear system by exact Gauss--Jordan elimination."""
    n = len(matrix)
    if n == 0 or len(rhs) != n or any(len(row) != n for row in matrix):
        raise ValueError("matrix must be nonempty and square")

    augmented = [list(row) + [rhs[i]] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next((r for r in range(col, n) if augmented[r][col]), None)
        if pivot is None:
            raise ValueError("singular matrix")
        if pivot != col:
            augmented[col], augmented[pivot] = augmented[pivot], augmented[col]

        pivot_value = augmented[col][col]
        augmented[col] = [v / pivot_value for v in augmented[col]]
        for r in range(n):
            if r == col:
                continue
            factor = augmented[r][col]
            if factor:
                augmented[r] = [
                    augmented[r][c] - factor * augmented[col][c]
                    for c in range(n + 1)
                ]
    return [augmented[i][-1] for i in range(n)]


def recover_geometric_coefficients(
    samples: Sequence[Fraction], start_n: int, q: Fraction = Q
) -> List[Fraction]:
    r"""Recover C_m in q_n=sum_{m=0}^M C_m q^(m(n+1)).

    The input consists of q_start_n,...,q_(start_n+M).  We first solve for
    B_m=C_m q^(m(start_n+1)) from the q-Vandermonde system

        sample_j = sum_m B_m q^(jm),

    then undo the common scale.
    """
    if start_n < 0 or not samples:
        raise ValueError("invalid starting index or empty sample list")
    M = len(samples) - 1
    vandermonde = [
        [q ** (j * m) for m in range(M + 1)] for j in range(M + 1)
    ]
    scaled = solve_fraction_system(vandermonde, samples)
    return [scaled[m] / q ** (m * (start_n + 1)) for m in range(M + 1)]


def annihilator_coefficients(M: int, q: Fraction = Q) -> List[Fraction]:
    r"""Coefficients A_j in prod_{m=0}^M(E-q^m)=sum_j A_j E^j."""
    coeffs: List[Fraction] = []
    for j in range(M + 2):
        exponent = (M + 1 - j) * (M - j) // 2
        coeffs.append(
            ((-1) ** (M + 1 - j))
            * q**exponent
            * gaussian_binomial(M + 1, j, q)
        )
    return coeffs


def verify_point(x: Fraction, holdout_count: int = 3) -> Tuple[bool, dict]:
    """Verify extraction, mode formula, and recurrence for one dyadic point."""
    if abs(x) > 1:
        raise ValueError("x must lie in [-1,1]")
    d = dyadic_depth(x)
    M = d // 2
    start_n = d

    samples = [finite_up(start_n + j, x) for j in range(M + 1)]
    limit = extract_limit(samples)
    coefficients = recover_geometric_coefficients(samples, start_n)
    if coefficients[0] != limit:
        return False, {"reason": "constant coefficient mismatch"}

    # Test values not used in the fit.
    for n in range(start_n, start_n + M + 1 + holdout_count):
        predicted = sum(
            coefficients[m] * Q ** (m * (n + 1)) for m in range(M + 1)
        )
        observed = finite_up(n, x)
        if predicted != observed:
            return False, {
                "reason": "geometric model mismatch",
                "x": x,
                "n": n,
                "predicted": predicted,
                "observed": observed,
            }

    # Test the shift-annihilating recurrence on a separate block.
    recurrence = annihilator_coefficients(M)
    for n in range(start_n, start_n + holdout_count):
        residual = sum(
            recurrence[j] * finite_up(n + j, x) for j in range(M + 2)
        )
        if residual:
            return False, {
                "reason": "annihilating recurrence mismatch",
                "x": x,
                "n": n,
                "residual": residual,
            }

    return True, {
        "x": x,
        "depth": d,
        "degree": M,
        "start_n": start_n,
        "samples": samples,
        "weights": extraction_weights(M),
        "limit": limit,
        "coefficients": coefficients,
    }


def fmt_list(values: Iterable[Fraction]) -> str:
    return "[" + ", ".join(str(v) for v in values) + "]"


def print_example(x: Fraction) -> None:
    ok, data = verify_point(x, holdout_count=4)
    if not ok:
        raise AssertionError(data)
    print(f"x = {x}")
    print(f"  reduced dyadic depth d = {data['depth']}")
    print(f"  geometric degree M=floor(d/2) = {data['degree']}")
    print(f"  samples q_n,...,q_(n+M), n=d: {fmt_list(data['samples'])}")
    print(f"  extraction weights:             {fmt_list(data['weights'])}")
    print(f"  extracted up(x):                {data['limit']}")
    print(f"  coefficients C_0,...,C_M:       {fmt_list(data['coefficients'])}")
    print("  unused-level checks and q-binomial recurrence: exact\n")


def exhaustive_regression(max_depth: int = 6) -> int:
    """Check every reduced nonintegral dyadic point through max_depth."""
    checked = 0
    for d in range(1, max_depth + 1):
        denominator = 1 << d
        # Odd numerators are exactly the reduced points of depth d.
        for numerator in range(-denominator + 1, denominator, 2):
            x = Fraction(numerator, denominator)
            ok, data = verify_point(x, holdout_count=2)
            if not ok:
                raise AssertionError(data)
            checked += 1

    # The three integer points are trivial fixed sequences: 0, 1, 0.
    for x, expected in [
        (Fraction(-1), Fraction(0)),
        (Fraction(0), Fraction(1)),
        (Fraction(1), Fraction(0)),
    ]:
        for n in range(7):
            observed = finite_up(n, x)
            if observed != expected:
                raise AssertionError((x, n, observed, expected))
        checked += 1
    return checked


def main() -> None:
    print("Exact dyadic extraction for finite sinc-product splines")
    print("Q = 1/4; all displayed values are exact fractions.\n")

    for x in [
        Fraction(1, 4),
        Fraction(1, 8),
        Fraction(1, 16),
        Fraction(3, 16),
        Fraction(5, 32),
    ]:
        print_example(x)

    checked = exhaustive_regression(max_depth=6)
    print(
        "Exhaustive regression through reduced denominator 2^6: "
        f"{checked} points checked; every residual was exactly zero."
    )


if __name__ == "__main__":
    main()
