#!/usr/bin/env python3
"""Exact verifier for the volume "Exact Dyadic Extraction of Rvachev's
Up-Function from Finite Sinc-Product Splines" (consolidated 2026-09-03).

Adapted from the verifier shipped with source S4 of the consolidation; the
additions are the checks in `verify_volume_claims`.  Running the script
with no arguments writes nothing.

Original description follows.


The user-indexed finite approximation is

    Q_n(x) = up_n(x)
           = F^{-1}[prod_{k=0}^n sinc(pi*t/2^k)](x).

Internally, p_N denotes the product with N factors, so Q_n = p_{n+1}.
All arithmetic used for dyadic sample values and extrapolation weights is exact
(`fractions.Fraction`).  The script:

1. evaluates finite box splines by the Thue--Morse truncated-power formula;
2. computes the q-Pochhammer/q-binomial extraction weights at q=1/4;
3. solves the exact geometric Vandermonde system for all correction terms;
4. verifies the eventual law on every reduced dyadic point of depth <= 7;
5. writes human-readable CSV/TXT tables and two illustrative figures.

No numerical quadrature or floating-point fitting is used in the exact tests.
Floating-point conversion is used only for plotting.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial, floor
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

Q = Fraction(1, 4)  # geometric base for the even-power error modes


def thue_morse_sign(k: int) -> int:
    """Return (-1)^(binary digit sum of k)."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    return -1 if k.bit_count() & 1 else 1


def is_power_of_two(n: int) -> bool:
    return n > 0 and (n & (n - 1)) == 0


def dyadic_depth(x: Fraction) -> int:
    """Smallest s >= 0 for which 2^s*x is an integer.

    Fraction automatically reduces the input, so the denominator is exactly 2^s.
    """
    x = Fraction(x)
    if not is_power_of_two(x.denominator):
        raise ValueError(f"{x} is not dyadic")
    return x.denominator.bit_length() - 1


def q_pochhammer(q: Fraction, n: int) -> Fraction:
    """Finite q-Pochhammer (q;q)_n = product_{r=1}^n (1-q^r)."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    out = Fraction(1)
    for r in range(1, n + 1):
        out *= 1 - q**r
    return out


def gaussian_binomial(n: int, k: int, q: Fraction) -> Fraction:
    """Gaussian binomial [n choose k]_q by q-Pochhammer quotients."""
    if k < 0 or k > n:
        return Fraction(0)
    return q_pochhammer(q, n) / (q_pochhammer(q, k) * q_pochhammer(q, n - k))


def extraction_weights(d: int, q: Fraction = Q) -> List[Fraction]:
    r"""Weights W_{d,j} that extract the constant from degree-d data at q^j.

    W_{d,j} = (-1)^(d-j) q^binom(d-j+1,2)
              / ((q;q)_j (q;q)_{d-j}).
    """
    if d < 0:
        raise ValueError("d must be nonnegative")
    result: List[Fraction] = []
    for j in range(d + 1):
        r = d - j
        exponent = r * (r + 1) // 2
        sign = -1 if r & 1 else 1
        result.append(
            sign * q**exponent / (q_pochhammer(q, j) * q_pochhammer(q, r))
        )
    return result


def finite_prefix_value(x: Fraction, N: int) -> Fraction:
    r"""Exact N-factor finite spline p_N(x).

    p_N is the inverse Fourier transform of
        prod_{k=0}^{N-1} sinc(pi*t/2^k).

    The implementation uses
        p_N(x) = 2^{N(N-1)/2}/(N-1)! *
                 sum_k tau_k (x+A_N-k/2^{N-1})_+^{N-1},
        A_N = 1-2^{-N}.

    Values at the two jump points of p_1 depend on Fourier inversion convention;
    every theorem verified below starts at N>=2 when such ambiguity is absent.
    """
    x = Fraction(x)
    if N < 1:
        raise ValueError("N must be at least 1")

    A_N = Fraction(1) - Fraction(1, 2**N)
    if x < -A_N or x > A_N:
        return Fraction(0)

    degree = N - 1
    y = 2 ** (N - 1) * (x + A_N)
    last = y.numerator // y.denominator

    # At all theorem-relevant dyadic midpoints y is a half-integer.  The integer
    # form below is substantially faster and avoids constructing one Fraction
    # per summand.
    two_y = 2 * y
    if two_y.denominator == 1:
        Y = two_y.numerator
        total_int = 0
        for k in range(last + 1):
            total_int += thue_morse_sign(k) * (Y - 2 * k) ** degree
        denominator = 2 ** (N * (N - 1) // 2) * factorial(degree)
        return Fraction(total_int, denominator)

    total = Fraction(0)
    for k in range(last + 1):
        total += thue_morse_sign(k) * (y - k) ** degree
    denominator = 2 ** ((N - 1) * (N - 2) // 2) * factorial(degree)
    return total / denominator


@lru_cache(maxsize=None)
def user_approximation(x: Fraction, n: int) -> Fraction:
    """User-indexed Q_n(x)=up_n(x)=p_{n+1}(x)."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    return finite_prefix_value(Fraction(x), n + 1)


def extract_up_value(x: Fraction, start: int | None = None) -> Fraction:
    """Extract up(x) from d+1 consecutive finite approximants.

    For dyadic depth s and d=floor(s/2), any start >= s is valid.
    """
    x = Fraction(x)
    s = dyadic_depth(x)
    d = s // 2
    n0 = s if start is None else start
    if n0 < s:
        raise ValueError(f"start={n0} is too early; the guaranteed threshold is s={s}")
    return sum(
        w * user_approximation(x, n0 + j)
        for j, w in enumerate(extraction_weights(d))
    )


def solve_linear_system(matrix: Sequence[Sequence[Fraction]], rhs: Sequence[Fraction]) -> List[Fraction]:
    """Gauss-Jordan elimination over the rationals."""
    n = len(rhs)
    if len(matrix) != n or any(len(row) != n for row in matrix):
        raise ValueError("matrix must be square and match rhs")
    aug = [list(map(Fraction, matrix[r])) + [Fraction(rhs[r])] for r in range(n)]

    for col in range(n):
        pivot = next((r for r in range(col, n) if aug[r][col] != 0), None)
        if pivot is None:
            raise ArithmeticError("singular matrix")
        aug[col], aug[pivot] = aug[pivot], aug[col]
        pivot_value = aug[col][col]
        aug[col] = [v / pivot_value for v in aug[col]]
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col]
            if factor:
                aug[r] = [aug[r][c] - factor * aug[col][c] for c in range(n + 1)]
    return [aug[r][-1] for r in range(n)]


def fit_geometric_law(x: Fraction, start: int | None = None) -> List[Fraction]:
    r"""Recover C_0,...,C_d in Q_n=C_0+sum_{m=1}^d C_m q^{mn}.

    The system is formed from Q_{n0},...,Q_{n0+d}; all operations are exact.
    """
    x = Fraction(x)
    s = dyadic_depth(x)
    d = s // 2
    n0 = s if start is None else start
    if n0 < s:
        raise ValueError(f"start={n0} is too early; the guaranteed threshold is s={s}")

    # First solve for A_m=C_m q^{m n0} from R(q^j)=Q_{n0+j}.
    matrix = [[Q ** (j * m) for m in range(d + 1)] for j in range(d + 1)]
    rhs = [user_approximation(x, n0 + j) for j in range(d + 1)]
    scaled = solve_linear_system(matrix, rhs)
    return [scaled[m] / Q ** (m * n0) for m in range(d + 1)]


def bernoulli_numbers(n: int) -> List[Fraction]:
    """Return B_0,...,B_n (Akiyama-Tanigawa; even B_{2m} are standard)."""
    A = [Fraction(0) for _ in range(n + 1)]
    B: List[Fraction] = []
    for m in range(n + 1):
        A[m] = Fraction(1, m + 1)
        for j in range(m, 0, -1):
            A[j - 1] = j * (A[j - 1] - A[j])
        B.append(A[0])
    return B


def reciprocal_sinc_coefficients(max_m: int) -> List[Fraction]:
    r"""Return a_0,...,a_max_m in 1/Phi(z)=sum a_m(2*pi*z)^{2m}.

    alpha_j = |B_{2j}| / (2j (2j)! (1-2^{-2j}))
    and m a_m = sum_{j=1}^m j alpha_j a_{m-j}.
    """
    if max_m < 0:
        raise ValueError("max_m must be nonnegative")
    B = bernoulli_numbers(2 * max_m)
    alpha = [Fraction(0)] * (max_m + 1)
    for j in range(1, max_m + 1):
        alpha[j] = abs(B[2 * j]) / (
            2 * j * factorial(2 * j) * (1 - Fraction(1, 2) ** (2 * j))
        )
    a = [Fraction(0)] * (max_m + 1)
    a[0] = Fraction(1)
    for m in range(1, max_m + 1):
        a[m] = sum(j * alpha[j] * a[m - j] for j in range(1, m + 1)) / m
    return a


def local_cell_data(x: Fraction, derivative_order: int) -> Tuple[int, Fraction]:
    r"""Return (k,y) with x=-1+(2k+1+y)/2^r and -1<=y<1.

    The formula is used only for -1<x<1 and r>=1.
    """
    x = Fraction(x)
    r = derivative_order
    if not (-1 < x < 1) or r < 1:
        raise ValueError("requires -1<x<1 and positive derivative order")
    k = floor(Fraction(2 ** (r - 1)) * (1 + x))
    y = 2**r * (1 + x) - (2 * k + 1)
    if not (Fraction(-1) <= y < Fraction(1)):
        raise AssertionError((x, r, k, y))
    return k, y


def predicted_geometric_coefficients(x: Fraction) -> List[Fraction]:
    r"""Coefficients predicted by exact local deconvolution and derivative tiling."""
    x = Fraction(x)
    s = dyadic_depth(x)
    d = s // 2
    coeffs = reciprocal_sinc_coefficients(d)
    result = [extract_up_value(x)]
    for m in range(1, d + 1):
        r = 2 * m
        k, y = local_cell_data(x, r)
        derivative = (
            2 ** (r * (r + 1) // 2)
            * thue_morse_sign(k)
            * extract_up_value(y)
        )
        C_m = (-1 if m & 1 else 1) * coeffs[m] * Fraction(1, 4**m) * derivative
        result.append(C_m)
    return result


def recurrence_residual(x: Fraction, n: int) -> Fraction:
    """Apply prod_{m=0}^d(E-q^m) to Q_n; should be zero for n>=depth."""
    s = dyadic_depth(x)
    d = s // 2
    # Polynomial coefficients in ascending powers of E.
    poly = [Fraction(1)]
    for m in range(d + 1):
        root = Q**m
        new = [Fraction(0)] * (len(poly) + 1)
        for j, c in enumerate(poly):
            new[j] -= root * c
            new[j + 1] += c
        poly = new
    return sum(c * user_approximation(x, n + j) for j, c in enumerate(poly))


@dataclass(frozen=True)
class VerificationSummary:
    max_depth: int
    point_count: int
    sequence_checks: int
    coefficient_checks: int
    recurrence_checks: int


def reduced_dyadics_at_depth(s: int) -> Iterable[Fraction]:
    if s == 0:
        yield Fraction(-1)
        yield Fraction(0)
        yield Fraction(1)
        return
    bound = 2**s
    for a in range(-bound + 1, bound, 2):
        yield Fraction(a, bound)


def verify_all(max_depth: int = 7) -> VerificationSummary:
    """Run exact theorem checks on all reduced dyadics through max_depth."""
    point_count = 0
    sequence_checks = 0
    coefficient_checks = 0
    recurrence_checks = 0

    for s in range(max_depth + 1):
        for x in reduced_dyadics_at_depth(s):
            point_count += 1
            d = s // 2
            L = extract_up_value(x)

            # The extracted constant must be independent of any later valid window.
            for shift in range(4):
                assert extract_up_value(x, s + shift) == L
                sequence_checks += 1

            # The full geometric coefficients from data match the analytic formula.
            fitted = fit_geometric_law(x)
            if -1 < x < 1 and d > 0:
                predicted = predicted_geometric_coefficients(x)
                assert fitted == predicted, (x, fitted, predicted)
                coefficient_checks += d + 1
            else:
                assert fitted[0] == L
                coefficient_checks += 1

            # Check continuation beyond the fitting window.
            for n in range(s, s + 6):
                value = sum(fitted[m] * Q ** (m * n) for m in range(d + 1))
                assert value == user_approximation(x, n), (x, n, value, user_approximation(x, n))
                sequence_checks += 1
                assert recurrence_residual(x, n) == 0, (x, n, recurrence_residual(x, n))
                recurrence_checks += 1

    return VerificationSummary(
        max_depth=max_depth,
        point_count=point_count,
        sequence_checks=sequence_checks,
        coefficient_checks=coefficient_checks,
        recurrence_checks=recurrence_checks,
    )


def frac_text(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def write_sample_sequences(out_dir: Path) -> None:
    samples = [
        Fraction(3, 4),
        Fraction(7, 8),
        Fraction(15, 16),
        Fraction(5, 16),
        Fraction(31, 32),
        Fraction(63, 64),
    ]
    path = out_dir / "sample_sequences.csv"
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(
            [
                "x",
                "dyadic_depth_s",
                "mode_count_d",
                "start_n",
                "approximation_q_n",
                "exact_up_x",
                "error_q_n_minus_up",
            ]
        )
        for x in samples:
            s = dyadic_depth(x)
            d = s // 2
            L = extract_up_value(x)
            for n in range(s, s + 7):
                qn = user_approximation(x, n)
                writer.writerow(
                    [frac_text(x), s, d, n, frac_text(qn), frac_text(L), frac_text(qn - L)]
                )


def write_coefficients(out_dir: Path) -> None:
    samples = [
        Fraction(3, 4),
        Fraction(7, 8),
        Fraction(15, 16),
        Fraction(5, 16),
        Fraction(31, 32),
        Fraction(63, 64),
    ]
    path = out_dir / "geometric_coefficients.csv"
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["x", "s", "d", "m", "C_m_in_q_n=sum_Cm_4^(-m*n)"])
        for x in samples:
            s = dyadic_depth(x)
            coeffs = fit_geometric_law(x)
            for m, c in enumerate(coeffs):
                writer.writerow([frac_text(x), s, s // 2, m, frac_text(c)])


def plot_figures(out_dir: Path) -> None:
    """Generate two figures; exact claims do not depend on these plots."""
    try:
        import matplotlib.pyplot as plt
    except ImportError:
        return

    def finite_prefix_float(x: float, N: int) -> float:
        A = 1.0 - 2.0 ** (-N)
        if x <= -A or x >= A:
            # All N>=2 curves are continuous and vanish at support endpoints.
            return 0.0
        degree = N - 1
        y = (2.0 ** (N - 1)) * (x + A)
        last = int(floor(y))
        total = 0.0
        for k in range(last + 1):
            total += thue_morse_sign(k) * max(y - k, 0.0) ** degree
        return total / (2.0 ** ((N - 1) * (N - 2) / 2.0) * factorial(degree))

    xs = [-1.0 + 2.0 * j / 800 for j in range(801)]
    plt.figure(figsize=(7.2, 4.5))
    for N in (2, 3, 4, 5, 6):
        ys = [finite_prefix_float(x, N) for x in xs]
        plt.plot(xs, ys, label=rf"$p_{{{N}}}$")
    plt.xlabel("x")
    plt.ylabel("finite spline value")
    plt.title("Inverse transforms of finite dyadic sinc products")
    plt.legend()
    plt.tight_layout()
    plt.savefig(out_dir / "finite_splines.pdf")
    plt.savefig(out_dir / "finite_splines.png", dpi=180)
    plt.close()

    x = Fraction(15, 16)
    L = extract_up_value(x)
    ns = list(range(4, 13))
    raw_errors = [abs(float(user_approximation(x, n) - L)) for n in ns]
    one_mode_errors = []
    w1 = extraction_weights(1)
    for n in ns:
        accelerated = w1[0] * user_approximation(x, n) + w1[1] * user_approximation(x, n + 1)
        one_mode_errors.append(abs(float(accelerated - L)))

    plt.figure(figsize=(7.2, 4.5))
    plt.semilogy(ns, raw_errors, marker="o", label=r"$|Q_n-u(x)|$")
    plt.semilogy(ns, one_mode_errors, marker="s", label="after cancelling $4^{-n}$")
    plt.xlabel("n")
    plt.ylabel("absolute error")
    plt.title(r"Geometric mode cancellation at $x=15/16$")
    plt.legend()
    plt.tight_layout()
    plt.savefig(out_dir / "geometric_mode_cancellation.pdf")
    plt.savefig(out_dir / "geometric_mode_cancellation.png", dpi=180)
    plt.close()


def write_summary(out_dir: Path, summary: VerificationSummary) -> None:
    a = reciprocal_sinc_coefficients(5)
    lines = [
        "Exact verification summary",
        "==========================",
        f"Maximum reduced dyadic depth: {summary.max_depth}",
        f"Dyadic points tested: {summary.point_count}",
        f"Sequence/window identities checked: {summary.sequence_checks}",
        f"Analytic-vs-fitted coefficient entries checked: {summary.coefficient_checks}",
        f"Annihilating recurrence checks: {summary.recurrence_checks}",
        "All checks passed using fractions.Fraction exact arithmetic.",
        "",
        "Reciprocal-sinc coefficients a_m:",
    ]
    for m, value in enumerate(a):
        lines.append(f"a_{m} = {frac_text(value)}")
    lines.extend(["", "Extraction weights at q=1/4:"])
    for d in range(5):
        lines.append(f"d={d}: " + ", ".join(frac_text(w) for w in extraction_weights(d)))
    (out_dir / "verification_report.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")


# ---------------------------------------------------------------------------
# Checks added in the consolidated volume (2026-09-03).  They test the claims
# that the six source reports state but whose verifiers never exercised.
# ---------------------------------------------------------------------------

PRINTED_A = [
    Fraction(1), Fraction(1, 18), Fraction(31, 16200),
    Fraction(2347, 42865200), Fraction(1904369, 1311675120000),
    Fraction(3309760579, 88561680752160000),
]


def reversed_extraction_weights(d: int, q: Fraction = Q) -> List[Fraction]:
    """S6's form of the row, applied to the samples in the order N+d, ..., N."""
    denom = q_pochhammer(q, d)
    return [
        (-1) ** j * q ** (j * (j + 1) // 2) * gaussian_binomial(d, j, q) / denom
        for j in range(d + 1)
    ]


def lebesgue_factor(d: int, q: Fraction = Q) -> Fraction:
    """(-q;q)_d / (q;q)_d, the exact l-infinity amplification of the row."""
    num = Fraction(1)
    for k in range(1, d + 1):
        num *= 1 + q ** k
    return num / q_pochhammer(q, d)


@dataclass(frozen=True)
class ExtraSummary:
    odd_onset_checks: int
    even_knot_points: int
    even_knot_failures: int
    nonzero_mode_checks: int
    reversed_row_checks: int
    lebesgue_checks: int
    knot_defect_checks: int


def verify_volume_claims(max_depth: int = 7) -> ExtraSummary:
    """The six additional claims, all in exact rational arithmetic.

    The sixth is the volume's closed form for the defect at the knot level
    n = s-1 (Theorem "Exact defect at the knot level"): with k the index of x
    in the knot lattice t_{s-1,k} = -1 + (2k+1) 2^{-s} and eps_k its Thue--Morse
    sign,  up_{s-1}(x) - [law at n = s-1]  =  -eps_k 2^{-C(s,2)} beta_s,  where
    beta_s = B_s / s! for even s and 0 for odd s.  It subsumes the odd-onset
    check (beta_s = 0) and explains every even-depth failure exactly.
    """
    assert reciprocal_sinc_coefficients(5) == PRINTED_A, reciprocal_sinc_coefficients(5)
    bern = bernoulli_numbers(max_depth + 1)

    knot_defect = 0
    odd_onset = 0
    even_pts = 0
    even_fail = 0
    nonzero = 0
    reversed_rows = 0
    lebesgue = 0
    for s in range(2, max_depth + 1):
        d = s // 2
        w = extraction_weights(d)
        wr = reversed_extraction_weights(d)
        # 5. Lebesgue factor, once per depth
        assert sum(abs(x) for x in w) == lebesgue_factor(d), (d, w)
        lebesgue += 1
        for x in reduced_dyadics_at_depth(s):
            if not (-1 < x < 1):
                continue
            fitted = fit_geometric_law(x)          # value = sum_m fitted[m] Q^(m n)
            # 2. every mode nonzero
            for m in range(1, d + 1):
                assert fitted[m] != 0, (x, m, fitted)
                nonzero += 1
            # 1. onset one level early
            law_prev = sum(fitted[m] * Q ** (m * (s - 1)) for m in range(d + 1))
            actual_prev = user_approximation(x, s - 1)
            if s % 2 == 1:
                assert law_prev == actual_prev, ("odd-onset failure", x, s)
                odd_onset += 1
            else:
                even_pts += 1
                if law_prev != actual_prev:
                    even_fail += 1
            # 6. exact knot-level defect
            k2 = 2 ** s * (x + 1) - 1
            assert k2.denominator == 1 and int(k2) % 2 == 0, (x, s)
            k = int(k2) // 2
            beta = bern[s] / factorial(s) if s % 2 == 0 else Fraction(0)
            predicted_defect = -thue_morse_sign(k) * Fraction(1, 2 ** comb(s, 2)) * beta
            assert actual_prev - law_prev == predicted_defect, ("knot defect", x, s, actual_prev - law_prev, predicted_defect)
            knot_defect += 1
            # 4. reversed row equals forward row
            N = s
            forward = sum(w[j] * user_approximation(x, N + j) for j in range(d + 1))
            backward = sum(wr[j] * user_approximation(x, N + d - j) for j in range(d + 1))
            assert forward == backward == fitted[0], (x, forward, backward, fitted[0])
            reversed_rows += 1
    return ExtraSummary(odd_onset, even_pts, even_fail, nonzero, reversed_rows, lebesgue, knot_defect)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=None,
        help="if given, write the CSV/TXT tables there; by default nothing is written",
    )
    parser.add_argument(
        "--max-depth",
        type=int,
        default=7,
        help="largest reduced dyadic depth for exhaustive exact verification",
    )
    parser.add_argument(
        "--plots",
        action="store_true",
        help="also write the two figures (imports matplotlib; needs --out-dir)",
    )
    args = parser.parse_args()

    summary = verify_all(args.max_depth)
    extra = verify_volume_claims(args.max_depth)
    print(summary)
    print(extra)
    print(
        "All exact checks passed; the even-depth knot level n = s-1 violates the law at "
        f"{extra.even_knot_failures} of {extra.even_knot_points} interior points, by exactly "
        f"-eps_k 2^(-C(s,2)) B_s/s! at every one of the {extra.knot_defect_checks} interior points of depth >= 2."
    )

    if args.out_dir is not None:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        write_sample_sequences(args.out_dir)
        write_coefficients(args.out_dir)
        write_summary(args.out_dir, summary)
        if args.plots:
            plot_figures(args.out_dir)
        print(f"Wrote outputs to {args.out_dir}")


if __name__ == "__main__":
    main()
