#!/usr/bin/env python3
"""Reproducible experiments for the dyadic Radon-profile report.

The script tests identities derived in the accompanying manuscript.  It does
not call a black-box implementation of the Fabius or Rvachev functions.
Instead it works directly with the direction profile c_h, its cumulative sinc
exponents a_j, the integer-zero multiplicities m_v, and the exact generating
functions

    A(q) = C(q)/(1-q),   M(q) = C(q)/(1-q)^2.

The only floating-point calculation is the high-frequency Fourier-envelope
experiment.  All profile inversion, sign, Prouhet, cumulant-ratio, and Hankel
checks use exact Python integers or fractions whenever possible.

Run from the archive root:

    python numerical_experiments.py --output-dir .

Dependencies: numpy, matplotlib, mpmath, sympy.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Callable, Dict, Iterable, List, Sequence, Tuple

import mpmath as mp
import numpy as np
import matplotlib.pyplot as plt
import sympy as sp


# ---------------------------------------------------------------------------
# Exact profile algebra
# ---------------------------------------------------------------------------


def v2(n: int) -> int:
    """Return the 2-adic valuation of a positive integer."""
    if n <= 0:
        raise ValueError("v2 expects a positive integer")
    return (n & -n).bit_length() - 1


def cumulative_exponents(c: Sequence[int], max_j: int) -> List[int]:
    """Return a_j = sum_{h <= j} c_h through max_j."""
    out: List[int] = []
    running = 0
    for j in range(max_j + 1):
        if j < len(c):
            running += int(c[j])
        out.append(running)
    return out


def zero_profile_from_c(c: Sequence[int], max_v: int) -> Tuple[List[int], List[int]]:
    """Return (a_j, m_v), where m_v = sum_{j <= v} a_j."""
    a = cumulative_exponents(c, max_v)
    m: List[int] = []
    running = 0
    for value in a:
        running += value
        m.append(running)
    return a, m


def invert_zero_profile(m: Sequence[int]) -> List[int]:
    """Recover c_v = m_v - 2m_{v-1} + m_{v-2}."""
    out: List[int] = []
    for v, value in enumerate(m):
        m1 = m[v - 1] if v >= 1 else 0
        m2 = m[v - 2] if v >= 2 else 0
        out.append(int(value - 2 * m1 + m2))
    return out


def polynomial_c_value(c: Sequence[int], q: Fraction) -> Fraction:
    """Evaluate a finite C(q)=sum c_h q^h exactly."""
    total = Fraction(0)
    power = Fraction(1)
    for coeff in c:
        total += int(coeff) * power
        power *= q
    return total


def m_from_formula(c: Sequence[int], v: int) -> int:
    """Direct triangular formula m_v=sum_{h<=v} c_h(v-h+1)."""
    return sum(int(c[h]) * (v - h + 1) for h in range(min(v + 1, len(c))))


# ---------------------------------------------------------------------------
# Digital signs and exact Prouhet cancellation
# ---------------------------------------------------------------------------


def sign_from_profile(a: Sequence[int], n: int) -> int:
    """Sign on the interval (n,n+1), using digit parity alpha_j=a_j mod 2."""
    exponent = 0
    j = 0
    x = n
    while x:
        if x & 1:
            exponent ^= int(a[j] & 1)
        x >>= 1
        j += 1
    return -1 if exponent else 1


def sign_from_zero_crossings(a: Sequence[int], n: int) -> int:
    """Same sign computed as parity of all crossed zeros."""
    exponent = sum(int(a[j]) * (n // (1 << j)) for j in range(len(a)))
    return -1 if exponent & 1 else 1


def prouhet_sums(signs: Sequence[int], max_degree: int) -> List[int]:
    """Return sum_n signs[n] n^k for 0<=k<=max_degree."""
    return [sum(int(s) * (n**k) for n, s in enumerate(signs)) for k in range(max_degree + 1)]


def pascal_a(rank: int, max_j: int) -> List[int]:
    """Pascal-Rvachev exponent a_j=binom(j,rank-1)."""
    return [math.comb(j, rank - 1) if j >= rank - 1 else 0 for j in range(max_j + 1)]


def pascal_c(rank: int, max_h: int) -> List[int]:
    """Direction multiplicity for the Pascal factorization.

    For rank 1 this is one copy at scale zero.  For rank r>=2,
    c_h=binom(h-1,r-2), supported on h>=r-1.
    """
    if rank == 1:
        return [1] + [0] * max_h
    return [
        math.comb(h - 1, rank - 2) if h >= rank - 1 else 0
        for h in range(max_h + 1)
    ]


# ---------------------------------------------------------------------------
# Cumulant ratios and Hausdorff moment checks
# ---------------------------------------------------------------------------


def cumulant_ratio(c: Sequence[int], n: int) -> Fraction:
    """R_n=C(4^{-n})=kappa_{2n}(Y_c)/kappa_{2n}(X)."""
    if n < 1:
        raise ValueError("n must be positive")
    return polynomial_c_value(c, Fraction(1, 4**n))


def forward_differences(values: Sequence[Fraction], order: int) -> List[Fraction]:
    """Compute an exact forward-difference row."""
    row = list(values)
    for _ in range(order):
        row = [row[i + 1] - row[i] for i in range(len(row) - 1)]
    return row


def hankel_determinants(moment_values: Sequence[Fraction], max_size: int) -> List[Fraction]:
    """Exact leading Hankel determinants from mu_0,mu_1,... ."""
    dets: List[Fraction] = []
    for size in range(1, max_size + 1):
        matrix = sp.Matrix(
            [
                [sp.Rational(moment_values[i + j].numerator, moment_values[i + j].denominator)
                 for j in range(size)]
                for i in range(size)
            ]
        )
        det = sp.factor(matrix.det())
        dets.append(Fraction(int(sp.numer(det)), int(sp.denom(det))))
    return dets


# ---------------------------------------------------------------------------
# Zero-divisor Dirichlet series
# ---------------------------------------------------------------------------


def zero_zeta_partial(c: Sequence[int], s: mp.mpf, nmax: int) -> mp.mpf:
    """Partial sum sum_{n<=N} m_{v2(n)} n^{-s}."""
    max_v = int(math.log2(nmax)) if nmax > 0 else 0
    _, m = zero_profile_from_c(c, max_v)
    return mp.fsum(mp.mpf(m[v2(n)]) / mp.power(n, s) for n in range(1, nmax + 1))


def C_mpf(c: Sequence[int], q: mp.mpf) -> mp.mpf:
    """Finite profile polynomial evaluated with mpmath."""
    total = mp.mpf("0")
    power = mp.mpf("1")
    for coeff in c:
        total += coeff * power
        power *= q
    return total


def zero_zeta_closed(c: Sequence[int], s: mp.mpf) -> mp.mpf:
    """Closed expression zeta(s) C(2^{-s})/(1-2^{-s})."""
    q = mp.power(2, -s)
    return mp.zeta(s) * C_mpf(c, q) / (1 - q)


# ---------------------------------------------------------------------------
# High-frequency logarithmic envelope
# ---------------------------------------------------------------------------


def exponent_polynomial(degree: int, j: int) -> int:
    """Use a_j=(j+1)^degree; its leading coefficient is one."""
    return (j + 1) ** degree


def log_abs_sinc_pi_small(x: mp.mpf) -> mp.mpf:
    """Stable log|sin(pi*x)/(pi*x)| for small or moderate nonzero x."""
    if x == 0:
        return mp.mpf("0")
    return mp.log(abs(mp.sin(mp.pi * x) / (mp.pi * x)))


def log_product_on_sharp_ray(degree: int, H: int, tail_terms: int = 180) -> mp.mpf:
    """Compute log|Psi(2^H/3)| without underflow.

    For j<=H the sine amplitude is exactly sqrt(3)/2, so those terms are
    evaluated by a closed logarithmic formula.  The rapidly convergent tail is
    evaluated with high precision.
    """
    ln2 = mp.log(2)
    log_const = mp.log(3 * mp.sqrt(3) / (2 * mp.pi))
    main = mp.fsum(
        exponent_polynomial(degree, j) * (log_const - (H - j) * ln2)
        for j in range(H + 1)
    )
    tail = mp.mpf("0")
    for j in range(H + 1, H + 1 + tail_terms):
        x = mp.power(2, H - j) / 3
        tail += exponent_polynomial(degree, j) * log_abs_sinc_pi_small(x)
    return main + tail


def predicted_envelope_constant(degree: int) -> mp.mpf:
    """Leading constant for a_j~j^degree."""
    return -1 / ((degree + 1) * (degree + 2) * mp.power(mp.log(2), degree + 1))


# ---------------------------------------------------------------------------
# Output helpers
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ExampleProfile:
    name: str
    c_builder: Callable[[int], List[int]]
    description: str


def write_csv(path: Path, fieldnames: Sequence[str], rows: Iterable[Dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def fraction_string(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def make_outputs(root: Path) -> None:
    data_dir = root / "data"
    figures_dir = root / "figures"
    data_dir.mkdir(parents=True, exist_ok=True)
    figures_dir.mkdir(parents=True, exist_ok=True)

    mp.mp.dps = 90

    # ---------------- Profile inversion and zero multiplicities ----------------
    max_v = 18
    examples = [
        ExampleProfile("classical", lambda H: [1] + [0] * H,
                       "one rank-one Rvachev coordinate"),
        ExampleProfile("finite_stack", lambda H: [1, 2, 1, 0, 3] + [0] * max(0, H - 4),
                       "finite mixed-scale projection"),
        ExampleProfile("all_scales", lambda H: [1] * (H + 1),
                       "one independent coordinate at every dyadic scale"),
        ExampleProfile("sparse_powers", lambda H: [1 if h == 0 or (h & (h - 1) == 0) else 0
                                                    for h in range(H + 1)],
                       "sparse shells at powers of two"),
    ]

    profile_rows: List[Dict[str, object]] = []
    inversion_failures = []
    for example in examples:
        c = example.c_builder(max_v)
        a, m = zero_profile_from_c(c, max_v)
        recovered = invert_zero_profile(m)
        if recovered != c[: max_v + 1]:
            inversion_failures.append(example.name)
        for h in range(max_v + 1):
            profile_rows.append({
                "profile": example.name,
                "h": h,
                "c_h": c[h],
                "a_h": a[h],
                "m_h": m[h],
                "delta2_m_h": recovered[h],
            })
    write_csv(
        data_dir / "profile_inversion.csv",
        ["profile", "h", "c_h", "a_h", "m_h", "delta2_m_h"],
        profile_rows,
    )
    if inversion_failures:
        raise AssertionError(f"profile inversion failed: {inversion_failures}")

    # Plot direction and zero profiles for a finite mixed-scale example.
    c_plot = examples[1].c_builder(max_v)
    a_plot, m_plot = zero_profile_from_c(c_plot, max_v)
    x = np.arange(max_v + 1)
    plt.figure(figsize=(8.4, 5.0))
    plt.step(x, c_plot, where="mid", label=r"direction multiplicity $c_h$")
    plt.step(x, a_plot, where="mid", label=r"sinc exponent $a_h$")
    plt.step(x, m_plot, where="mid", label=r"zero profile $m_h$")
    plt.xlabel("dyadic shell / valuation index")
    plt.ylabel("integer value")
    plt.title("Triangular integration and exact second-difference recovery")
    plt.legend()
    plt.tight_layout()
    plt.savefig(figures_dir / "profile_inversion.pdf")
    plt.savefig(figures_dir / "profile_inversion.png", dpi=180)
    plt.close()

    # ---------------- Pascal factorization ----------------
    pascal_rows: List[Dict[str, object]] = []
    max_h = 16
    for rank in range(1, 7):
        c = pascal_c(rank, max_h)
        a = cumulative_exponents(c, max_h)
        target_a = pascal_a(rank, max_h)
        if a != target_a:
            raise AssertionError(f"Pascal factorization failed at rank {rank}")
        for h in range(max_h + 1):
            pascal_rows.append({
                "rank": rank,
                "h": h,
                "c_h": c[h],
                "cumulative_a_h": a[h],
                "target_binomial": target_a[h],
            })
    write_csv(
        data_dir / "pascal_factorization.csv",
        ["rank", "h", "c_h", "cumulative_a_h", "target_binomial"],
        pascal_rows,
    )

    norm_rows: List[Dict[str, object]] = []
    for rank in range(1, 7):
        for p in [1, 2, 4, 6, 8]:
            # Closed norm sum.  Rank one is a single unit coefficient at h=0.
            closed = mp.mpf(1) if rank == 1 else mp.power(mp.power(2, p) - 1, -(rank - 1))
            # A long finite sum checks the identity independently.
            c = pascal_c(rank, 180)
            partial = mp.fsum(c[h] * mp.power(2, -p * h) for h in range(len(c)))
            norm_rows.append({
                "rank": rank,
                "p": p,
                "partial_sum": mp.nstr(partial, 28),
                "closed_form": mp.nstr(closed, 28),
                "absolute_error": mp.nstr(abs(partial - closed), 8),
            })
    write_csv(
        data_dir / "pascal_norms.csv",
        ["rank", "p", "partial_sum", "closed_form", "absolute_error"],
        norm_rows,
    )

    # ---------------- Digital signs and Prouhet checks ----------------
    sign_profiles: Dict[str, List[int]] = {}
    width = 1024
    max_bits = int(math.log2(width))
    sign_profiles["classical Thue-Morse"] = [1] * (max_bits + 2)
    sign_profiles["eventually even exponent"] = cumulative_exponents([1, 1], max_bits + 1)
    sign_profiles["Pascal rank 3"] = pascal_a(3, max_bits + 1)
    sparse_c = [1 if h == 0 or (h > 0 and (h & (h - 1) == 0)) else 0
                for h in range(max_bits + 2)]
    sign_profiles["sparse nonperiodic shells"] = cumulative_exponents(sparse_c, max_bits + 1)

    sign_matrix = []
    sign_rows: List[Dict[str, object]] = []
    for name, a in sign_profiles.items():
        signs = [sign_from_profile(a, n) for n in range(width)]
        crossing = [sign_from_zero_crossings(a, n) for n in range(width)]
        if signs != crossing:
            raise AssertionError(f"sign formula disagreement for {name}")
        sign_matrix.append([1 if s < 0 else 0 for s in signs])
        for n in range(128):
            sign_rows.append({"profile": name, "n": n, "sign": signs[n]})
    write_csv(data_dir / "sign_prefixes.csv", ["profile", "n", "sign"], sign_rows)

    plt.figure(figsize=(11.0, 3.3))
    plt.imshow(np.array(sign_matrix), aspect="auto", interpolation="nearest")
    plt.yticks(range(len(sign_profiles)), list(sign_profiles.keys()))
    plt.xlabel("interval index N (negative signs are highlighted by the image scale)")
    plt.title("Generalized spectral sign sequences")
    plt.tight_layout()
    plt.savefig(figures_dir / "digital_signs.pdf")
    plt.savefig(figures_dir / "digital_signs.png", dpi=180)
    plt.close()

    prouhet_rows: List[Dict[str, object]] = []
    for name, a in sign_profiles.items():
        for M in range(3, min(max_bits, 9) + 1):
            signs = [sign_from_profile(a, n) for n in range(1 << M)]
            d_M = sum((a[j] & 1) for j in range(M))
            sums = prouhet_sums(signs, min(d_M + 1, 12))
            verified = all(value == 0 for value in sums[:d_M])
            if not verified:
                raise AssertionError(f"Prouhet cancellation failed for {name}, M={M}")
            first_nonzero = sums[d_M] if d_M < len(sums) else "not computed"
            prouhet_rows.append({
                "profile": name,
                "M": M,
                "block_length": 1 << M,
                "predicted_order": d_M,
                "all_lower_power_sums_zero": verified,
                "degree_d_sum": first_nonzero,
            })
    write_csv(
        data_dir / "prouhet_checks.csv",
        ["profile", "M", "block_length", "predicted_order",
         "all_lower_power_sums_zero", "degree_d_sum"],
        prouhet_rows,
    )

    # ---------------- Cumulant-ratio Hausdorff moment problem ----------------
    c_moment = [2, 1, 3, 1, 2, 2, 1]
    R = [cumulant_ratio(c_moment, n) for n in range(1, 18)]
    difference_rows: List[Dict[str, object]] = []
    complete_monotone_ok = True
    for k in range(0, 9):
        row = forward_differences(R, k)
        signed = [((-1) ** k) * value for value in row]
        if any(value < 0 for value in signed):
            complete_monotone_ok = False
        for n, value in enumerate(signed, start=1):
            difference_rows.append({
                "difference_order": k,
                "n": n,
                "signed_difference": fraction_string(value),
                "nonnegative": value >= 0,
            })
    if not complete_monotone_ok:
        raise AssertionError("complete monotonicity check failed")
    write_csv(
        data_dir / "complete_monotonicity.csv",
        ["difference_order", "n", "signed_difference", "nonnegative"],
        difference_rows,
    )

    # R_{n+1} is the moment sequence mu_n of the finite positive dyadic measure.
    mu = R  # mu_0=R_1, mu_1=R_2, ...
    hankel = hankel_determinants(mu, 6)
    hankel_rows = [
        {"size": i + 1, "determinant": fraction_string(value), "positive": value > 0}
        for i, value in enumerate(hankel)
    ]
    write_csv(data_dir / "hankel_determinants.csv", ["size", "determinant", "positive"], hankel_rows)

    plt.figure(figsize=(8.2, 5.0))
    n_values = np.arange(1, len(R) + 1)
    plt.semilogy(n_values, [float(value) for value in R], marker="o", label=r"$R_n=C(4^{-n})$")
    for k in [1, 2, 3]:
        row = forward_differences(R, k)
        signed = [float(((-1) ** k) * value) for value in row]
        plt.semilogy(np.arange(1, len(signed) + 1), signed, marker="o",
                     label=rf"$(-1)^{k}\Delta^{k}R_n$")
    plt.xlabel("n")
    plt.ylabel("exact quantity (plotted as float)")
    plt.title("Complete monotonicity of the normalized even-cumulant ratios")
    plt.legend()
    plt.tight_layout()
    plt.savefig(figures_dir / "cumulant_ratio_moments.pdf")
    plt.savefig(figures_dir / "cumulant_ratio_moments.png", dpi=180)
    plt.close()

    # ---------------- Zero-divisor zeta formula ----------------
    zeta_c = [1, 2, 0, 3, 1]
    zeta_s = mp.mpf("3.75")
    zeta_exact = zero_zeta_closed(zeta_c, zeta_s)
    zeta_rows: List[Dict[str, object]] = []
    for nmax in [100, 1000, 10000, 100000, 500000]:
        partial = zero_zeta_partial(zeta_c, zeta_s, nmax)
        zeta_rows.append({
            "N": nmax,
            "partial_sum": mp.nstr(partial, 30),
            "closed_form": mp.nstr(zeta_exact, 30),
            "absolute_error": mp.nstr(abs(partial - zeta_exact), 12),
        })
    write_csv(
        data_dir / "zero_zeta_convergence.csv",
        ["N", "partial_sum", "closed_form", "absolute_error"],
        zeta_rows,
    )

    # ---------------- Sharp Fourier envelope ----------------
    envelope_rows: List[Dict[str, object]] = []
    H_values = list(range(8, 81, 4)) + [90, 100, 120, 140, 160, 200, 250, 300, 400, 500]
    plt.figure(figsize=(8.4, 5.2))
    for degree in range(4):
        ratios = []
        predicted = predicted_envelope_constant(degree)
        for H in H_values:
            log_value = log_product_on_sharp_ray(degree, H)
            xH_log = H * mp.log(2) - mp.log(3)
            ratio = log_value / mp.power(xH_log, degree + 2)
            ratios.append(float(ratio))
            envelope_rows.append({
                "degree_d": degree,
                "H": H,
                "log_x": mp.nstr(xH_log, 24),
                "log_abs_product": mp.nstr(log_value, 30),
                "normalized_ratio": mp.nstr(ratio, 24),
                "predicted_constant": mp.nstr(predicted, 24),
                "difference": mp.nstr(ratio - predicted, 12),
            })
        plt.plot(H_values, ratios, marker="o", label=rf"$d={degree}$")
        plt.axhline(float(predicted), linewidth=0.8)
    plt.xlabel(r"dyadic ray index $H$ in $x_H=2^H/3$")
    plt.ylabel(r"$\log|\Psi(x_H)|/(\log x_H)^{d+2}$")
    plt.title("Convergence to the sharp logarithmic Fourier-envelope constant")
    plt.legend()
    plt.tight_layout()
    plt.savefig(figures_dir / "fourier_envelope.pdf")
    plt.savefig(figures_dir / "fourier_envelope.png", dpi=180)
    plt.close()
    write_csv(
        data_dir / "fourier_envelope.csv",
        ["degree_d", "H", "log_x", "log_abs_product", "normalized_ratio",
         "predicted_constant", "difference"],
        envelope_rows,
    )

    # ---------------- A compact TeX table and human-readable summary ----------------
    final_by_degree = {}
    for row in envelope_rows:
        final_by_degree[int(row["degree_d"])] = row

    tex_lines = [
        r"\begin{tabular}{rrrr}",
        r"\toprule",
        r"$d$ & $H$ & observed ratio & predicted constant\\",
        r"\midrule",
    ]
    for degree in range(4):
        row = final_by_degree[degree]
        tex_lines.append(
            f"{degree} & {row['H']} & {mp.nstr(mp.mpf(str(row['normalized_ratio'])), 10)} & "
            f"{mp.nstr(mp.mpf(str(row['predicted_constant'])), 10)}\\\\"
        )
    tex_lines.extend([r"\bottomrule", r"\end{tabular}"])
    (data_dir / "fourier_envelope_table.tex").write_text("\n".join(tex_lines) + "\n", encoding="utf-8")

    summary_lines = [
        "DYADIC RADON-PROFILE NUMERICAL SUMMARY",
        "========================================",
        "",
        f"Profile inversion exact for {len(examples)} test families through valuation {max_v}.",
        "Pascal factorization exact for ranks 1 through 6 and shells 0 through 16.",
        f"Digital sign identity checked for {len(sign_profiles)} families and N<={width-1}.",
        f"All Prouhet power-sum cancellations predicted by parity were verified in {len(prouhet_rows)} blocks.",
        f"Complete monotonicity of R_n=C(4^(-n)) checked through difference order 8: {complete_monotone_ok}.",
        "Leading exact Hankel determinants for the shifted ratio sequence:",
    ]
    for i, det in enumerate(hankel, start=1):
        summary_lines.append(f"  size {i}: {fraction_string(det)}")
    summary_lines.extend([
        "",
        f"Zero-divisor Dirichlet identity checked at s={zeta_s}; final truncation error "
        f"{zeta_rows[-1]['absolute_error']}.",
        "",
        "Sharp-ray Fourier envelope at the largest H:",
    ])
    for degree in range(4):
        row = final_by_degree[degree]
        summary_lines.append(
            f"  d={degree}: observed {row['normalized_ratio']}, predicted {row['predicted_constant']}, "
            f"difference {row['difference']}"
        )
    summary_lines.extend([
        "",
        "All checks completed without assertion failures.",
    ])
    (root / "numerical_results.txt").write_text("\n".join(summary_lines) + "\n", encoding="utf-8")



def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("."),
        help="archive root receiving data/, figures/, and numerical_results.txt",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    root = args.output_dir.resolve()
    root.mkdir(parents=True, exist_ok=True)
    make_outputs(root)
    print((root / "numerical_results.txt").read_text(encoding="utf-8"))


if __name__ == "__main__":
    main()
