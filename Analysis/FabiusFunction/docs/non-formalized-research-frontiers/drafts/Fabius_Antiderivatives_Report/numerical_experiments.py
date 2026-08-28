#!/usr/bin/env python3
"""Numerical and exact checks for the report
"Antiderivatives of Monomially Weighted Fabius-Type Functions".

The script deliberately avoids a black-box point evaluator for the Fabius
function.  Instead it uses two independent moment recurrences:

  * d_n = E[X^n], where X has the Fabius distribution;
  * c_n = E[(2X-1)^(2n)], the even moments of Rvachev's up density.

The d_n recurrence follows from the Fabius moment generating function
G(2z) = ((exp(z)-1)/z) G(z).  The c_n recurrence follows independently from
H(2z) = (sinh(z)/z) H(z), where H is the MGF of 2X-1.

These two moment systems allow us to check the arbitrary-power Newton series
against the centered-moment formula, to verify exact finite identities with
rational arithmetic, and to evaluate the logarithmic constant
    integral_0^1 F(x)/x dx = -E[log X]
in two different rapidly convergent ways.

Only mpmath and the Python standard library are required.
"""

from __future__ import annotations

import argparse
import csv
import math
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

import mpmath as mp


def exact_fabius_moments(count: int) -> list[Fraction]:
    """Return d_0,...,d_count exactly as Fractions.

    Recurrence (n >= 1):
      (n+1)(2^n-1)d_n = sum_{k=0}^{n-1} C(n+1,k)d_k.
    """
    d = [Fraction(1, 1)]
    for n in range(1, count + 1):
        numerator = sum(Fraction(math.comb(n + 1, k), 1) * d[k] for k in range(n))
        denominator = (n + 1) * (2**n - 1)
        d.append(numerator / denominator)
    return d


def exact_centered_moments(count: int) -> list[Fraction]:
    """Return c_0,...,c_count exactly as Fractions.

    Here c_n = E[(2X-1)^(2n)].  From
      H(2z) = (sinh z / z) H(z)
    one obtains, for n >= 1,
      (4^n-1)c_n = sum_{k=0}^{n-1} C(2n,2k)c_k/(2(n-k)+1).
    """
    c = [Fraction(1, 1)]
    for n in range(1, count + 1):
        numerator = sum(
            Fraction(math.comb(2 * n, 2 * k), 2 * (n - k) + 1) * c[k]
            for k in range(n)
        )
        c.append(numerator / (4**n - 1))
    return c


def mp_fabius_moments(count: int) -> list[mp.mpf]:
    """High-precision floating-point version of the d_n recurrence."""
    d = [mp.mpf(1)]
    for n in range(1, count + 1):
        total = mp.mpf(0)
        binom = mp.mpf(1)  # C(n+1,0)
        for k in range(n):
            total += binom * d[k]
            binom *= mp.mpf(n + 1 - k) / mp.mpf(k + 1)
        d.append(total / ((n + 1) * (mp.power(2, n) - 1)))
    return d


def mp_centered_moments(count: int) -> list[mp.mpf]:
    """High-precision floating-point version of the c_n recurrence."""
    c = [mp.mpf(1)]
    for n in range(1, count + 1):
        total = mp.mpf(0)
        binom_even = mp.mpf(1)  # C(2n,0)
        for k in range(n):
            total += binom_even * c[k] / (2 * (n - k) + 1)
            # C(2n,2k+2) / C(2n,2k)
            binom_even *= (
                mp.mpf(2 * n - 2 * k)
                * mp.mpf(2 * n - 2 * k - 1)
                / (mp.mpf(2 * k + 1) * mp.mpf(2 * k + 2))
            )
        c.append(total / (mp.power(4, n) - 1))
    return c


def falling(alpha: mp.mpf | mp.mpc, k: int) -> mp.mpf | mp.mpc:
    """Falling factorial alpha^(underline k), evaluated stably by recurrence."""
    result: mp.mpf | mp.mpc = mp.mpf(1)
    for j in range(k):
        result *= alpha - j
    return result


def newton_antiderivative(alpha: mp.mpf | mp.mpc, d: Sequence[mp.mpf]) -> mp.mpf | mp.mpc:
    r"""Truncated Newton--Fabius series for integral_0^1 x^alpha F(x) dx.

      A(alpha) = sum_{k>=0} (-1)^k alpha^(underline k) d_{k+1}/(k+1)!

    The implementation updates the falling factorial and factorial recursively.
    """
    total: mp.mpf | mp.mpc = mp.mpf(0)
    fall: mp.mpf | mp.mpc = mp.mpf(1)
    factorial = mp.mpf(1)  # (k+1)! at k=0 is 1
    sign = mp.mpf(1)
    for k in range(len(d) - 1):
        if k > 0:
            fall *= alpha - (k - 1)
            factorial *= k + 1
            sign = -sign
        total += sign * fall * d[k + 1] / factorial
    return total


def centered_power_moment(s: mp.mpf | mp.mpc, c: Sequence[mp.mpf]) -> mp.mpf | mp.mpc:
    r"""Compute M(s)=E[X^s] from centered moments.

      M(s) = 2^(-s) sum_{q>=0} C(s,2q)c_q.

    The binomial coefficients are updated two factors at a time.
    """
    total: mp.mpf | mp.mpc = c[0]
    binom_even: mp.mpf | mp.mpc = mp.mpf(1)  # C(s,0)
    for q in range(1, len(c)):
        n = 2 * q
        binom_even *= (s - (n - 2)) * (s - (n - 1)) / ((n - 1) * n)
        total += binom_even * c[q]
    return mp.power(2, -s) * total


def centered_antiderivative(alpha: mp.mpf | mp.mpc, c: Sequence[mp.mpf]) -> mp.mpf | mp.mpc:
    """Independent evaluation through (1-M(alpha+1))/(alpha+1)."""
    s = alpha + 1
    if abs(s) < mp.mpf("1e-40"):
        # Removable value -M'(0) = log 2 + 1/2 sum_{q>=1} c_q/q.
        return mp.log(2) + mp.fsum(c[q] / (2 * q) for q in range(1, len(c)))
    return (1 - centered_power_moment(s, c)) / s


def exact_integer_identity_table(max_p: int, d: Sequence[Fraction]) -> list[tuple[int, Fraction, Fraction]]:
    """Check the terminating p-th-power identity exactly."""
    rows: list[tuple[int, Fraction, Fraction]] = []
    for p in range(max_p + 1):
        lhs = Fraction(0, 1)
        for r in range(p + 1):
            coefficient = Fraction(((-1) ** r) * math.factorial(p), math.factorial(p - r))
            lhs += coefficient * d[r + 1] / math.factorial(r + 1)
        rhs = (Fraction(1, 1) - d[p + 1]) / (p + 1)
        if lhs != rhs:
            raise AssertionError(f"integer identity failed for p={p}: {lhs} != {rhs}")
        rows.append((p, lhs, rhs))
    return rows


def exact_two_parameter_identity(max_n: int, max_p: int, d: Sequence[Fraction]) -> None:
    r"""Verify the two-parameter finite-difference identity exactly.

      sum_{r=0}^p (-1)^r C(p,r)d_{n+r}/(n+r)
      = sum_{j=0}^{n-1} (-1)^j C(n-1,j)(1-d_{p+j+1})/(p+j+1).
    """
    for n in range(1, max_n + 1):
        for p in range(max_p + 1):
            lhs = sum(
                Fraction(((-1) ** r) * math.comb(p, r), 1) * d[n + r] / (n + r)
                for r in range(p + 1)
            )
            rhs = sum(
                Fraction(((-1) ** j) * math.comb(n - 1, j), 1)
                * (Fraction(1, 1) - d[p + j + 1])
                / (p + j + 1)
                for j in range(n)
            )
            if lhs != rhs:
                raise AssertionError(
                    f"two-parameter identity failed for n={n}, p={p}: {lhs} != {rhs}"
                )


def mgf_from_moments(z: mp.mpf | mp.mpc, d: Sequence[mp.mpf]) -> mp.mpf | mp.mpc:
    """Evaluate G(z)=sum d_n z^n/n! from moments."""
    total: mp.mpf | mp.mpc = mp.mpf(0)
    term_power: mp.mpf | mp.mpc = mp.mpf(1)
    factorial = mp.mpf(1)
    for n, dn in enumerate(d):
        if n > 0:
            term_power *= z
            factorial *= n
        total += dn * term_power / factorial
    return total


def mgf_product(z: mp.mpf | mp.mpc, factors: int) -> mp.mpf | mp.mpc:
    r"""Independent product G(z)=prod_{j>=1}(exp(z/2^j)-1)/(z/2^j)."""
    product: mp.mpf | mp.mpc = mp.mpf(1)
    for j in range(1, factors + 1):
        w = z / mp.power(2, j)
        product *= mp.expm1(w) / w if w != 0 else 1
    return product


def format_mpf(value: mp.mpf | mp.mpc, digits: int = 32) -> str:
    """Compact deterministic formatting for text and CSV output."""
    return mp.nstr(value, n=digits, strip_zeros=False)


def run(output_dir: Path, d_count: int, c_count: int, dps: int) -> None:
    mp.mp.dps = dps
    output_dir.mkdir(parents=True, exist_ok=True)

    # Exact arithmetic checks.
    exact_limit = max(18, 8 + 8)
    d_exact = exact_fabius_moments(exact_limit)
    c_exact = exact_centered_moments(8)
    integer_rows = exact_integer_identity_table(8, d_exact)
    exact_two_parameter_identity(6, 8, d_exact)

    # High-precision moment arrays for nonintegral and negative powers.
    d = mp_fabius_moments(d_count)
    c = mp_centered_moments(c_count)

    alphas = [
        mp.mpf("0.5"),
        mp.mpf("-0.5"),
        mp.mpf("-1"),
        mp.mpf("-2"),
        mp.mpf("2.3"),
        mp.mpc("0.25", "0.4"),
    ]
    comparison_rows: list[dict[str, str]] = []
    for alpha in alphas:
        via_newton = newton_antiderivative(alpha, d)
        via_centered = centered_antiderivative(alpha, c)
        comparison_rows.append(
            {
                "alpha": format_mpf(alpha, 18),
                "newton_series": format_mpf(via_newton),
                "centered_moment_formula": format_mpf(via_centered),
                "absolute_difference": format_mpf(abs(via_newton - via_centered), 12),
            }
        )

    # The logarithmic constant has two positive series representations.
    log_constant_d = mp.fsum(d[n] / n for n in range(1, len(d)))
    log_constant_c = mp.log(2) + mp.fsum(c[q] / (2 * q) for q in range(1, len(c)))

    # Check the MGF recurrence/product and exponential-antiderivative master identity.
    z = mp.mpc("0.7", "0.2")
    g_series = mgf_from_moments(z, d[: min(len(d), 220)])
    g_product = mgf_product(z, max(80, int(mp.log(dps, 2)) + 20))
    mgf_difference = abs(g_series - g_product)
    exp_primitive_closed = (mp.exp(z) - g_product) / z
    exp_primitive_series = mp.exp(z) * mp.fsum(
        ((-z) ** (n - 1)) * d[n] / math.factorial(n)
        for n in range(1, min(len(d), 180))
    )

    csv_path = output_dir / "fractional_power_checks.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=comparison_rows[0].keys(), lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(comparison_rows)

    text_path = output_dir / "verification_output.txt"
    with text_path.open("w", encoding="utf-8") as handle:
        handle.write("Fabius antiderivative verification output\n")
        handle.write("=========================================\n\n")
        handle.write(f"mpmath precision: {dps} decimal digits\n")
        handle.write(f"d moments used: d_0 through d_{d_count}\n")
        handle.write(f"c moments used: c_0 through c_{c_count}\n\n")

        handle.write("First exact Fabius moments d_n = E[X^n]:\n")
        for n, value in enumerate(d_exact[:11]):
            handle.write(f"  d_{n} = {value}\n")
        handle.write("\nFirst exact centered even moments c_n = E[(2X-1)^(2n)]:\n")
        for n, value in enumerate(c_exact[:7]):
            handle.write(f"  c_{n} = {value}\n")

        handle.write("\nExact terminating identities (left side = right side):\n")
        for p, lhs, rhs in integer_rows:
            handle.write(f"  p={p}: {lhs} = {rhs}\n")
        handle.write("\nTwo-parameter identities checked exactly for 1 <= n <= 6, 0 <= p <= 8.\n")

        handle.write("\nArbitrary-power integral A(alpha)=integral_0^1 x^alpha F(x) dx:\n")
        for row in comparison_rows:
            handle.write(
                f"  alpha={row['alpha']}\n"
                f"    Newton series:   {row['newton_series']}\n"
                f"    centered moments:{row['centered_moment_formula']}\n"
                f"    abs difference:  {row['absolute_difference']}\n"
            )

        handle.write("\nLogarithmic constant integral_0^1 F(x)/x dx = -E[log X]:\n")
        handle.write(f"  sum d_n/n:                     {format_mpf(log_constant_d)}\n")
        handle.write(f"  log(2) + (1/2)sum c_n/n:       {format_mpf(log_constant_c)}\n")
        handle.write(f"  absolute difference:           {format_mpf(abs(log_constant_d-log_constant_c), 12)}\n")

        handle.write("\nMGF and exponential-master check at z=0.7+0.2i:\n")
        handle.write(f"  G from moments:                {format_mpf(g_series)}\n")
        handle.write(f"  G from infinite product:       {format_mpf(g_product)}\n")
        handle.write(f"  absolute difference:           {format_mpf(mgf_difference, 12)}\n")
        handle.write(f"  (exp(z)-G(z))/z:               {format_mpf(exp_primitive_closed)}\n")
        handle.write(f"  dyadic primitive series:       {format_mpf(exp_primitive_series)}\n")
        handle.write(
            f"  absolute difference:           {format_mpf(abs(exp_primitive_closed-exp_primitive_series), 12)}\n"
        )

    print(text_path.read_text(encoding="utf-8"))
    print(f"Wrote {csv_path}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="Directory for verification_output.txt and fractional_power_checks.csv",
    )
    parser.add_argument("--d-count", type=int, default=1500, help="Largest d_n index")
    parser.add_argument("--c-count", type=int, default=700, help="Largest c_n index")
    parser.add_argument("--dps", type=int, default=85, help="mpmath decimal precision")
    return parser.parse_args()


if __name__ == "__main__":
    args = parse_args()
    run(args.output_dir, args.d_count, args.c_count, args.dps)
