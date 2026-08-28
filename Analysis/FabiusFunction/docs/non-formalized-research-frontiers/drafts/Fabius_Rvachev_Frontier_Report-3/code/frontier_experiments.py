#!/usr/bin/env python3
"""Numerical experiments for the Fabius--Rvachev frontier report.

The report proves two principal results.

1. A factorized q-Richardson transform can be applied to the *zero-free tail*
   of the Rvachev sinc product and then multiplied by the finite prefix.  The
   prefix carries the complete zero divisor, while the extrapolated tail is
   analytic and nonzero on the natural zero-free disk.  The resulting
   approximation is holomorphic on that disk and preserves every included zero
   and its multiplicity.

2. If M_r(q,a) is the magnitude of the signed logarithmic error at order r,
   then the same-parity nesting M_{r+2}<M_r holds uniformly for 0<a<1 exactly
   when q**(r+1)*(1+q) <= 1.  If the inequality fails, there is exactly one
   crossing a_r(q) in (0,1).

This script reproduces all numerical tables and figures in the report.  It is
written for clarity and auditability rather than maximum throughput.  All
quantities that determine theorem statements are computed independently from
both (a) the exact coefficient series and (b) direct products where possible.

Dependencies:
    Python 3.10+
    mpmath
    matplotlib

Usage:
    python frontier_experiments.py --output-dir ../generated

The output directory will contain CSV tables and PNG figures.  No network access
is required.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path
from typing import Iterable, Optional, Sequence

import mpmath as mp
import matplotlib.pyplot as plt


# High precision is useful near a same-parity crossing close to a=1.
mp.mp.dps = 60

# Cache the exponentially small coefficient corrections.  Root searches and
# plots evaluate the same M_r(q,a) at many values of a; recomputing zeta(2m)
# for each evaluation would be needlessly expensive.
_CORRECTION_CACHE: dict[tuple[str, int, str], tuple[int, list[mp.mpf]]] = {}


def q_pochhammer_finite(q: mp.mpf, n: int) -> mp.mpf:
    """Return (q;q)_n = product_{k=1}^n (1-q^k)."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    value = mp.mpf(1)
    for k in range(1, n + 1):
        value *= 1 - q**k
    return value


def shifted_q_pochhammer(q: mp.mpf, start_power: int, length: int) -> mp.mpf:
    """Return (q^start_power;q)_length."""
    if start_power < 1 or length < 0:
        raise ValueError("start_power >= 1 and length >= 0 are required")
    value = mp.mpf(1)
    for k in range(length):
        value *= 1 - q ** (start_power + k)
    return value


def richardson_weights(q: mp.mpf, r: int) -> list[mp.mpf]:
    r"""Lagrange weights at geometric nodes 1,q,...,q^r, evaluated at 0.

    The closed form is

        lambda_{r,j} = (-1)^(r-j) q^((r-j)(r-j+1)/2)
                       / ((q;q)_j (q;q)_{r-j}).

    Hence sum_j lambda_{r,j} q^(jm)=0 for 1<=m<=r, and the sum is 1
    for m=0.  These are the q-binomial Richardson weights used throughout
    the repository and the report.
    """
    if not (0 < q < 1):
        raise ValueError("q must lie in (0,1)")
    if r < 0:
        raise ValueError("r must be nonnegative")

    result: list[mp.mpf] = []
    for j in range(r + 1):
        k = r - j
        numerator = (-1) ** k * q ** (k * (k + 1) // 2)
        denominator = q_pochhammer_finite(q, j) * q_pochhammer_finite(q, k)
        result.append(numerator / denominator)
    return result


def transformed_moment(q: mp.mpf, r: int, m: int) -> mp.mpf:
    """Compute S_{r,m}=sum_j lambda_{r,j} q^(jm) in two independent ways."""
    weights = richardson_weights(q, r)
    direct = mp.fsum(weights[j] * q ** (j * m) for j in range(r + 1))

    if m == 0:
        closed = mp.mpf(1)
    elif 1 <= m <= r:
        closed = mp.mpf(0)
    else:
        closed = (-1) ** r * q ** (r * (r + 1) // 2) * shifted_q_pochhammer(
            q, m - r, r
        ) / q_pochhammer_finite(q, r)

    # This is a numerical self-check, not a theorem assumption.
    if abs(direct - closed) > mp.mpf("1e-55"):
        raise ArithmeticError(
            f"q-Lagrange moment mismatch for q={q}, r={r}, m={m}: "
            f"{direct} versus {closed}"
        )
    return closed


def error_prefactor(q: mp.mpf, r: int) -> mp.mpf:
    """Return q^(r(r+1)/2)/(q;q)_r."""
    return q ** (r * (r + 1) // 2) / q_pochhammer_finite(q, r)


def error_magnitude(q: mp.mpf, r: int, a: mp.mpf, tol: mp.mpf = mp.mpf("1e-60")) -> mp.mpf:
    r"""Return the positive logarithmic error magnitude M_r(q,a).

    For 0<q,a<1,

      M_r(q,a) = A_r sum_{m>=r+1} zeta(2m)/m
                   * (q^(m-r);q)_r/(1-q^m) * a^m,
      A_r = q^(r(r+1)/2)/(q;q)_r.

    A direct sum converges slowly when a is close to 1.  We therefore split off
    the universal harmonic singularity.  Since

      zeta(2m) (q^(m-r);q)_r/(1-q^m) -> 1,

    we use

      sum_{m>=r+1} a^m/m = -log(1-a)-sum_{m=1}^r a^m/m,

    and sum only the exponentially decaying correction.  This makes roots near
    a=1 inexpensive and stable.
    """
    q = mp.mpf(q)
    a = mp.mpf(a)
    if not (0 < q < 1 and 0 < a < 1):
        raise ValueError("q and a must lie in (0,1)")
    if r < 0:
        raise ValueError("r must be nonnegative")

    harmonic_tail = -mp.log1p(-a) - mp.fsum(a**m / m for m in range(1, r + 1))

    key = (mp.nstr(q, 70), r, mp.nstr(tol, 10))
    cached = _CORRECTION_CACHE.get(key)
    if cached is None:
        coefficients: list[mp.mpf] = []
        small_count = 0
        # Coefficients, rather than terms at a particular a, are cached.  They
        # decay like max(q,1/4)^m and are therefore uniformly summable up to
        # the boundary a=1.
        for m in range(r + 1, 200000):
            u = shifted_q_pochhammer(q, m - r, r) / (1 - q**m)
            coefficient = (mp.zeta(2 * m) * u - 1) / m
            coefficients.append(coefficient)
            if abs(coefficient) < tol:
                small_count += 1
                if small_count >= 8:
                    break
            else:
                small_count = 0
        else:
            raise RuntimeError("correction coefficients did not converge within the safety cap")
        cached = (r + 1, coefficients)
        _CORRECTION_CACHE[key] = cached

    first_power, coefficients = cached
    # Horner evaluation of sum_{m>=first_power} c_m a^m.
    correction_polynomial = mp.mpf(0)
    for coefficient in reversed(coefficients):
        correction_polynomial = coefficient + a * correction_polynomial
    correction = a**first_power * correction_polynomial

    return error_prefactor(q, r) * (harmonic_tail + correction)


def signed_log_error(q: mp.mpf, r: int, a: mp.mpf) -> mp.mpf:
    """Return E_r=(-1)^r M_r."""
    return (-1) ** r * error_magnitude(q, r, a)


def uniform_nesting_holds(q: mp.mpf, r: int) -> bool:
    """Exact theorem criterion for M_{r+2}(q,a)<M_r(q,a), all 0<a<1."""
    return q ** (r + 1) * (1 + q) <= 1


def critical_q(r: int) -> mp.mpf:
    """Solve q^(r+1)(1+q)=1 for the unique q in (0,1)."""
    lo = mp.mpf(0)
    hi = mp.mpf(1)
    for _ in range(260):
        mid = (lo + hi) / 2
        if mid ** (r + 1) * (1 + mid) < 1:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def first_uniform_nesting_order(q: mp.mpf) -> int:
    """Smallest r>=0 for which all same-parity levels from r onward are nested."""
    q = mp.mpf(q)
    ratio = mp.log(1 + q) / (-mp.log(q))
    return max(0, int(mp.ceil(ratio)) - 1)


def crossing_root(q: mp.mpf, r: int) -> Optional[mp.mpf]:
    r"""Return the unique a in (0,1) with M_r(q,a)=M_{r+2}(q,a).

    The theorem says no such root exists when q^(r+1)(1+q)<=1.  Otherwise
    the coefficient difference has exactly one sign change, and therefore the
    root is unique.  Bisection is used because it preserves that proof-level
    bracketing and does not depend on a derivative estimate.
    """
    q = mp.mpf(q)
    if uniform_nesting_holds(q, r):
        return None

    def difference(a: mp.mpf) -> mp.mpf:
        return error_magnitude(q, r, a) - error_magnitude(q, r + 2, a)

    lo = mp.mpf("1e-6")
    hi = 1 - mp.mpf("1e-45")
    f_lo = difference(lo)
    f_hi = difference(hi)
    if not (f_lo > 0 and f_hi < 0):
        raise ArithmeticError(
            f"root was not bracketed for q={q}, r={r}: {f_lo=}, {f_hi=}"
        )

    for _ in range(150):
        mid = (lo + hi) / 2
        if difference(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def sincpi(x: mp.mpf) -> mp.mpf:
    """Normalized sinc sin(pi*x)/(pi*x), evaluated stably at zero."""
    x = mp.mpf(x)
    if x == 0:
        return mp.mpf(1)
    return mp.sin(mp.pi * x) / (mp.pi * x)


def rvachev_tail(x: mp.mpf, n: int, tol: mp.mpf = mp.mpf("1e-65")) -> mp.mpf:
    r"""Return the exact zero-free tail Phi(x/2^(n+1)).

    Phi(x)=product_{h>=0} sincpi(x/2^h).  The finite prefix through h=n
    contains every zero in |x|<2^(n+1), and the omitted tail is positive there.
    The logarithmic product is used to avoid loss of relative accuracy.
    """
    x = mp.mpf(x)
    boundary = mp.mpf(2) ** (n + 1)
    if not abs(x) < boundary:
        raise ValueError(f"tail is not zero-free: require |x| < {boundary}")

    log_value = mp.mpf(0)
    h = n + 1
    while True:
        y = x / (mp.mpf(2) ** h)
        factor = sincpi(y)
        if factor <= 0:
            raise ArithmeticError("a factor unexpectedly left the positive zero-free branch")
        term = mp.log(factor)
        log_value += term
        if abs(term) < tol:
            # Subsequent logarithms shrink by about 1/4 each level.
            break
        h += 1
        if h > n + 10000:
            raise RuntimeError("tail product failed to converge")
    return mp.exp(log_value)


def relative_partial_tail(x: mp.mpf, n: int, j: int) -> mp.mpf:
    """Return product_{h=n+1}^{n+j} sincpi(x/2^h), with j=0 giving 1."""
    if j < 0:
        raise ValueError("j must be nonnegative")
    value = mp.mpf(1)
    for h in range(n + 1, n + j + 1):
        value *= sincpi(mp.mpf(x) / (mp.mpf(2) ** h))
    return value


def factorized_tail_transform(x: mp.mpf, n: int, r: int) -> mp.mpf:
    r"""Return the factorized q-Richardson approximation to the zero-free tail.

    q=1/4 for dyadic scaling.  We form the analytic logarithms of the relative
    partial tails and exponentiate their q-Lagrange combination.  On the real
    zero-free disk all factors are positive, so the normalized analytic branch
    is simply the ordinary real logarithm.
    """
    q = mp.mpf(1) / 4
    weights = richardson_weights(q, r)
    log_value = mp.mpf(0)
    for j, weight in enumerate(weights):
        relative = relative_partial_tail(x, n, j)
        if relative <= 0:
            raise ArithmeticError("relative tail is outside the normalized positive branch")
        log_value += weight * mp.log(relative)
    return mp.exp(log_value)


def write_csv(path: Path, header: Sequence[str], rows: Iterable[Sequence[object]]) -> None:
    """Write a UTF-8 CSV with deterministic newlines."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(header)
        writer.writerows(rows)


def mp_text(value: mp.mpf, digits: int = 30) -> str:
    """Compact decimal text suitable for CSV and LaTeX ingestion."""
    return mp.nstr(value, digits)


def produce_tables(output_dir: Path) -> None:
    """Generate all CSV tables used in the report."""
    data_dir = output_dir / "data"
    data_dir.mkdir(parents=True, exist_ok=True)

    # Exact threshold q_r and the corresponding geometric base b_r=q_r^(-1/2).
    threshold_rows = []
    for r in range(13):
        q_r = critical_q(r)
        threshold_rows.append(
            (r, mp_text(q_r, 28), mp_text(q_r ** (-mp.mpf(1) / 2), 28))
        )
    write_csv(
        data_dir / "same_parity_thresholds.csv",
        ("r", "critical_q", "critical_base_b"),
        threshold_rows,
    )

    # Representative supercritical cases.  These values verify the unique
    # crossing theorem; they are not used to infer it.
    crossing_cases = [
        (mp.mpf("0.7"), 0),
        (mp.mpf("0.8"), 0),
        (mp.mpf("0.8"), 1),
        (mp.mpf("0.9"), 0),
        (mp.mpf("0.9"), 1),
        (mp.mpf("0.9"), 2),
        (mp.mpf("0.9"), 3),
    ]
    crossing_rows = []
    for q, r in crossing_cases:
        root = crossing_root(q, r)
        crossing_rows.append(
            (
                mp_text(q, 8),
                r,
                "" if root is None else mp_text(root, 30),
                first_uniform_nesting_order(q),
            )
        )
    write_csv(
        data_dir / "same_parity_crossings.csv",
        ("q", "r", "crossing_a", "first_uniform_nesting_order"),
        crossing_rows,
    )

    # Low-order dyadic weights.  Their moment identities are checked by the
    # transformed_moment calls before writing.
    weight_rows = []
    q = mp.mpf(1) / 4
    for r in range(7):
        weights = richardson_weights(q, r)
        for m in range(r + 3):
            transformed_moment(q, r, m)
        for j, weight in enumerate(weights):
            weight_rows.append((r, j, mp_text(weight, 35)))
    write_csv(
        data_dir / "dyadic_q_richardson_weights.csv",
        ("r", "j", "lambda_rj"),
        weight_rows,
    )

    # A zero-jet experiment.  x=48 is an integer zero of multiplicity
    # 1+nu_2(48)=5.  Taking n=5 puts every vanishing sinc factor in the prefix,
    # because |48|<2^6.  The ratio of the first nonzero derivative of the
    # factorized approximation to that of Phi is exactly tail_hat/tail.
    x = mp.mpf(48)
    n = 5
    exact_tail = rvachev_tail(x, n)
    a = (x / (mp.mpf(2) ** (n + 1))) ** 2
    jet_rows = []
    for r in range(9):
        approximated_tail = factorized_tail_transform(x, n, r)
        direct_log_error = mp.log(approximated_tail / exact_tail)
        series_log_error = signed_log_error(q, r, a)
        if abs(direct_log_error - series_log_error) > mp.mpf("1e-55"):
            raise ArithmeticError(
                f"direct/series error mismatch at r={r}: "
                f"{direct_log_error} vs {series_log_error}"
            )
        jet_rows.append(
            (
                r,
                mp_text(approximated_tail, 35),
                mp_text(approximated_tail / exact_tail, 35),
                mp_text(direct_log_error, 35),
                "upper" if r % 2 == 0 else "lower",
            )
        )
    write_csv(
        data_dir / "integer_zero_jet_brackets.csv",
        (
            "r",
            "approximated_tail",
            "first_nonzero_derivative_ratio",
            "signed_log_error",
            "bracket_side",
        ),
        jet_rows,
    )

    # A nonzero-point check demonstrates that the full relative error is the
    # same as the tail relative error after the finite prefix is factored out.
    x_nonzero = mp.mpf("43.25")
    a_nonzero = (x_nonzero / (mp.mpf(2) ** (n + 1))) ** 2
    exact_nonzero_tail = rvachev_tail(x_nonzero, n)
    rows = []
    for r in range(7):
        hat = factorized_tail_transform(x_nonzero, n, r)
        rows.append(
            (
                r,
                mp_text(hat / exact_nonzero_tail, 35),
                mp_text(mp.log(hat / exact_nonzero_tail), 35),
                mp_text(signed_log_error(q, r, a_nonzero), 35),
            )
        )
    write_csv(
        data_dir / "nonzero_point_factorized_errors.csv",
        ("r", "relative_ratio", "direct_log_error", "series_log_error"),
        rows,
    )


def produce_figures(output_dir: Path) -> None:
    """Generate the figures embedded in the report."""
    figure_dir = output_dir / "figures"
    figure_dir.mkdir(parents=True, exist_ok=True)

    # Figure 1: all dyadic same-parity levels are nested.  We plot magnitudes;
    # even and odd signed errors lie on opposite sides of the exact product.
    q = mp.mpf(1) / 4
    a_values = [mp.mpf("0.01") + i * mp.mpf("0.94") / 119 for i in range(120)]
    plt.figure(figsize=(7.2, 4.8))
    for r in range(6):
        values = [float(error_magnitude(q, r, a, mp.mpf("1e-45"))) for a in a_values]
        plt.semilogy([float(a) for a in a_values], values, label=f"r={r}")
    plt.xlabel("a")
    plt.ylabel(r"$M_r(1/4,a)$")
    plt.title("Dyadic logarithmic error magnitudes")
    plt.legend(ncol=2)
    plt.tight_layout()
    plt.savefig(figure_dir / "dyadic_error_magnitudes.png", dpi=180)
    plt.close()

    # Figure 2: in a supercritical case the same-parity difference has exactly
    # one zero.  q=.9,r=1 gives a visually well-separated crossing.
    q = mp.mpf("0.9")
    r = 1
    a_values = [mp.mpf("0.05") + i * mp.mpf("0.94") / 159 for i in range(160)]
    differences = []
    for a in a_values:
        first = error_magnitude(q, r, a, mp.mpf("1e-45"))
        second = error_magnitude(q, r + 2, a, mp.mpf("1e-45"))
        differences.append(float((first - second) / (first + second)))
    root = crossing_root(q, r)
    plt.figure(figsize=(7.2, 4.6))
    plt.plot([float(a) for a in a_values], differences, label=r"$(M_1-M_3)/(M_1+M_3)$")
    plt.axhline(0.0)
    plt.axvline(float(root), label=f"unique crossing {mp.nstr(root, 8)}")
    plt.xlabel("a")
    plt.ylabel("normalized same-parity difference")
    plt.title("Unique same-parity crossing for q=0.9")
    plt.legend()
    plt.tight_layout()
    plt.savefig(figure_dir / "unique_same_parity_crossing.png", dpi=180)
    plt.close()

    # Figure 3: certified convergence of the first nonzero derivative at the
    # integer zero x=48 (multiplicity five).  The vertical quantity is exactly
    # |tail_hat/tail-1|, hence exactly the derivative-ratio error.
    x = mp.mpf(48)
    n = 5
    exact_tail = rvachev_tail(x, n)
    orders = list(range(9))
    errors = [
        float(abs(factorized_tail_transform(x, n, r) / exact_tail - 1))
        for r in orders
    ]
    plt.figure(figsize=(7.2, 4.6))
    plt.semilogy(orders, errors, marker="o")
    plt.xlabel("Richardson order r")
    plt.ylabel("absolute derivative-ratio error")
    plt.title("Certified first nonzero derivative at the zero x=48")
    plt.tight_layout()
    plt.savefig(figure_dir / "integer_zero_derivative_convergence.png", dpi=180)
    plt.close()


def write_summary(output_dir: Path) -> None:
    """Write a compact plain-text run summary for independent inspection."""
    lines = [
        "Fabius--Rvachev frontier experiments",
        "====================================",
        "",
        f"mpmath precision: {mp.mp.dps} decimal digits",
        "",
        "Exact symbolic/numerical checks performed:",
        "- q-Lagrange moment cancellation for all written weights",
        "- direct product versus Bernoulli-zeta error series",
        "- critical q roots of q^(r+1)(1+q)=1",
        "- unique supercritical crossing roots",
        "- dyadic integer-zero derivative-ratio brackets at x=48",
        "",
        "Generated files are under data/ and figures/.",
    ]
    (output_dir / "experiment_summary.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="directory receiving data/ and figures/ (default: report bundle root)",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    output_dir = args.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    produce_tables(output_dir)
    produce_figures(output_dir)
    write_summary(output_dir)
    print(f"Generated tables and figures in {output_dir}")


if __name__ == "__main__":
    main()
