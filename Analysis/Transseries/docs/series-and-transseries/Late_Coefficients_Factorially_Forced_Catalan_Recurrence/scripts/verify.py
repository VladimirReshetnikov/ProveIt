#!/usr/bin/env python3
"""Reproduce exact coefficients and fixed-order numerical checks (stdlib only).

Requires Python >= 3.11. Run from any working directory, for example::

    python3 scripts/verify.py
    python3 scripts/verify.py --max-index 1000 --points 100 300 600 1000

The formal definitions are F(z)=sum n! z^n, A=F+z A^2,
D=(1-4zF)^(-1/2), H=2D^3, and
c_k=sum_{ell=0}^{k-1} d_{ell+1} S(k-1,ell), with c_0=1.

Exact integer arithmetic generates a,d,c through --max-index. Two independent
identities check D: its differential recurrence at every generated index, and
its literal binomial expansion through --binomial-order (40 by default).
The correction polynomials q_j are computed by a finite Stirling formula and
checked against the original bivariate power-series formula using Fractions.
Decimal arithmetic evaluates c_k (log 2)^k/(k-1)! directly; no floating-point
logarithms of huge integers, external sequence files, or network access are used.

Numerical residuals illustrate fixed-order asymptotics; they are not rigorous
finite-k error bounds or evidence of a uniform optimal-truncation theorem.
All results are deterministic. Output paths default to this project's results/.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import sys
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RESULTS = PROJECT_ROOT / "results"

# Numerical displayed prefixes read on 2026-10-02 from the official entries.
# Sources: https://oeis.org/A229741 and https://oeis.org/A260879
# These finite arrays are independent regression fixtures, not full entry texts.
OEIS_A229741 = [
    1, 2, 6, 22, 92, 428, 2208, 12756, 83848, 635392, 5563952, 55743168,
    628294912, 7832530400, 106515280064, 1564127939088, 24618706734432,
    413015301455040, 7352809011276096, 138398862650413248,
    2745596388858393984, 57248882869605962880, 1251574614271552264704,
    28625091198273426059136]
OEIS_A260879 = [
    1, 2, 8, 44, 288, 2148, 17816, 161852, 1594280, 16911940, 192361656,
    2340735564, 30460211400, 424505682772, 6355333371032, 102649319717020,
    1797042119668552, 34229646342692388, 710605915340085240,
    16058830502126670956, 393461778913536741064]


def require(condition: bool, message: str) -> None:
    """Raise on a failed check, including when Python is run with -O."""
    if not condition:
        raise ArithmeticError(message)


def factorials(n: int) -> list[int]:
    """Return 0!,...,n! using exact integer multiplication."""
    f = [1] * (n + 1)
    for k in range(2, n + 1):
        f[k] = k * f[k - 1]
    return f


def convolve(a: list[int], b: list[int], n: int) -> list[int]:
    """Truncated ordinary product through degree n."""
    out = [0] * (n + 1)
    for i, ai in enumerate(a[:n + 1]):
        for j, bj in enumerate(b[:n + 1 - i]):
            out[i + j] += ai * bj
    return out


def stirling_rows(n: int) -> list[list[int]]:
    """Return S(i,j), 0<=i<=n, by the second-kind Stirling recurrence."""
    rows = [[1]]
    for i in range(1, n + 1):
        previous = rows[-1]
        rows.append([0] + [previous[j - 1]
                           + (j * previous[j] if j < i else 0)
                           for j in range(1, i + 1)])
    return rows


def exact_sequences(n: int) -> tuple[list[int], list[int], list[int]]:
    """Compute a,d,c through index n with O(n^2) integer operations."""
    f = factorials(n)
    a = [1]
    d = [1]
    for k in range(1, n + 1):
        a.append(f[k] + sum(a[i] * a[k - 1 - i] for i in range(k)))
        d.append(2 * sum(a[i] * d[k - 1 - i] for i in range(k)))
    c = [1]
    row = [1]
    for k in range(1, n + 1):
        c.append(sum(d[ell + 1] * s for ell, s in enumerate(row)))
        row = [0] + [row[j - 1] + (j * row[j] if j < len(row) else 0)
                     for j in range(1, len(row) + 1)]
    return a, d, c


def differential_d(n: int) -> list[int]:
    """Independently compute D from (1-4G)D'=2G'D, G=zF.

    Thus n*d_n=sum_{r=1}^n (4*n-2*r)*(r-1)!*d_{n-r}.
    This construction does not use A or the A-dependent recurrence for D.
    """
    f = factorials(n)
    d = [1]
    for k in range(1, n + 1):
        numerator = sum((4 * k - 2 * r) * f[r - 1] * d[k - r]
                        for r in range(1, k + 1))
        require(numerator % k == 0, f"Nonintegral differential d_{k}")
        d.append(numerator // k)
    return d


def check_inverse_stirling(c: list[int], d: list[int]) -> None:
    """Check the entire c transform by exact signed first-kind inversion.

    d_(N+1)=sum_{k=0}^N s(N,k)c_(k+1), where s denotes signed
    Stirling numbers of the first kind. Large cancellations are exact.
    """
    row = [1]
    for n in range(len(c) - 1):
        recovered = sum(value * c[k + 1] for k, value in enumerate(row))
        require(recovered == d[n + 1], f"Inverse Stirling check failed at index {n + 1}")
        row = [0] + [row[k - 1] - (n * row[k] if k < len(row) else 0)
                     for k in range(1, len(row) + 1)]


def binomial_d_and_h(n: int) -> tuple[list[int], list[int]]:
    """Literal binomial expansions of D and H through degree n.

    D=sum_m binom(2m,m)*(zF)^m and
    H=2*sum_m (2m+1)*binom(2m,m)*(zF)^m.
    This deliberately independent check has O(n^3) arithmetic cost.
    """
    g = [0] + factorials(max(0, n - 1))[:n]
    power = [1] + [0] * n
    d, h = [0] * (n + 1), [0] * (n + 1)
    for m in range(n + 1):
        central = math.comb(2 * m, m)
        for k, value in enumerate(power):
            d[k] += central * value
            h[k] += 2 * (2 * m + 1) * central * value
        if m < n:
            power = convolve(power, g, n)
    return d, h


def corrections_stirling(h: list[int], order: int) -> list[list[int]]:
    """q_j as coefficient vectors in rho, generated without symbolic packages.

    q_j = sum_{v=0}^{j-1} rho^(v+1) S(j-1,v)
          * sum_{r=1}^{v+1} h_r 2^(r-1) S(v,r-1).

    The result has q[0]=[1], so q[0] also represents Q's constant term.
    """
    rows = stirling_rows(order)
    q = [[1]]
    for j in range(1, order + 1):
        coefficients = [0] * (j + 1)
        for v in range(j):
            coefficients[v + 1] = rows[j - 1][v] * sum(
                h[r] * 2 ** (r - 1) * rows[v][r - 1]
                for r in range(1, v + 2))
        q.append(coefficients)
    return q


def bivariate_product(a: dict[tuple[int, int], Fraction],
                      b: dict[tuple[int, int], Fraction],
                      y_limit: int) -> dict[tuple[int, int], Fraction]:
    """Multiply sparse polynomials in (y,rho), truncating the y-degree."""
    out: dict[tuple[int, int], Fraction] = {}
    for (ya, ra), av in a.items():
        for (yb, rb), bv in b.items():
            if ya + yb <= y_limit:
                key = (ya + yb, ra + rb)
                out[key] = out.get(key, Fraction(0)) + av * bv
    return out


def corrections_power_series(h: list[int], order: int) -> list[list[int]]:
    """Independently evaluate the original finite q generator over Q[y,rho].

    Build g=2*(exp(rho*(exp(y)-1))-1), which equals exp(rho*exp(y))-2
    at rho=log(2), then use
    q_j=rho*(j-1)!*sum_r h_r/(r-1)!*[y^(j-1)]g^(r-1).
    No Stirling numbers are used by this second calculation.
    """
    y_limit = order - 1
    inner = {(m, 1): Fraction(1, math.factorial(m))
             for m in range(1, y_limit + 1)}
    inner_power = {(0, 0): Fraction(1)}
    g: dict[tuple[int, int], Fraction] = {}
    for m in range(1, y_limit + 1):
        inner_power = bivariate_product(inner_power, inner, y_limit)
        for key, value in inner_power.items():
            g[key] = g.get(key, Fraction(0)) + 2 * value / math.factorial(m)
    powers = [{(0, 0): Fraction(1)}]
    for _ in range(1, order):
        powers.append(bivariate_product(powers[-1], g, y_limit))
    q = [[1]]
    for j in range(1, order + 1):
        coefficients = [Fraction(0)] * (j + 1)
        for r in range(1, j + 1):
            scale = Fraction(math.factorial(j - 1) * h[r],
                             math.factorial(r - 1))
            for (yd, rd), value in powers[r - 1].items():
                if yd == j - 1:
                    coefficients[rd + 1] += scale * value
        require(all(v.denominator == 1 for v in coefficients),
                f"Nonintegral q_{j} coefficients")
        q.append([int(v) for v in coefficients])
    return q


def polynomial_string(coefficients: list[int]) -> str:
    """Human-readable, deterministic polynomial with integer coefficients."""
    terms = []
    for exponent, coefficient in enumerate(coefficients):
        if coefficient:
            factor = "" if exponent == 0 else ("*rho" if exponent == 1
                                               else f"*rho^{exponent}")
            terms.append(f"{coefficient}{factor}")
    return " + ".join(terms) or "0"


def write_json(path: Path, value: object) -> None:
    """Write readable UTF-8 JSON with deterministic ordering and newline."""
    path.write_text(json.dumps(value, indent=2, ensure_ascii=True) + "\n",
                    encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, object]]) -> None:
    """Write deterministic CSV with explicit LF endings."""
    if not rows:
        return
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def normalized_checks(c: list[int], q: list[list[int]], points: list[int],
                      precision: int) -> list[dict[str, object]]:
    """Evaluate direct Decimal ratios and the J=1,3,6 partial sums."""
    rows = []
    with localcontext() as ctx:
        ctx.prec = precision
        rho = Decimal(2).ln()
        qvalues = [sum(Decimal(v) * rho ** i for i, v in enumerate(poly))
                   for poly in q]
        for k in points:
            ratio = Decimal(c[k]) * rho ** k / Decimal(math.factorial(k - 1))
            row: dict[str, object] = {"k": k, "normalized_ratio": format(ratio, ".40E")}
            for order in (1, 3, 6):
                approximation = Decimal(1) + sum(
                    qvalues[j] / Decimal(k - 1) ** j for j in range(1, order + 1))
                row[f"Q{order}"] = format(approximation, ".40E")
                row[f"residual_Q{order}"] = format(ratio - approximation, ".40E")
            rows.append(row)
    return rows


def main() -> None:
    """Command-line entry point; failed exact checks raise an exception."""
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-index", type=int, default=500, help="largest exact a,d,c index (default: 500)")
    parser.add_argument("--binomial-order", type=int, default=40,
                        help="literal binomial D/H check depth, O(depth^3) (default: 40)")
    parser.add_argument("--q-order", type=int, default=6,
                        help="number of exact correction polynomials, at least 6 (default: 6)")
    parser.add_argument("--precision", type=int, default=80,
                        help="Decimal working precision, at least 60 (default: 80)")
    parser.add_argument("--points", type=int, nargs="+", default=[20, 50, 100, 200, 350, 500],
                        help="indices for normalized ratios; each must be between 2 and max-index")
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_RESULTS)
    args = parser.parse_args()
    if sys.version_info < (3, 11):
        parser.error("Python 3.11 or newer is required")
    if args.q_order < 6 or args.precision < 60:
        parser.error("q-order must be >=6 and precision must be >=60")
    if args.max_index < max(6, args.q_order) or not (args.q_order <= args.binomial_order <= args.max_index):
        parser.error("Require max-index >= binomial-order >= q-order >= 6")
    if any(k < 2 or k > args.max_index for k in args.points):
        parser.error("Each point must be between 2 and max-index")
    sys.set_int_max_str_digits(0)  # Only locally computed integers are serialized.
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    a, d, c = exact_sequences(args.max_index)
    require(d == differential_d(args.max_index), "Full differential D check failed")
    check_inverse_stirling(c, d)
    binomial_d, binomial_h = binomial_d_and_h(args.binomial_order)
    require(d[:args.binomial_order + 1] == binomial_d, "Literal binomial D check failed")
    h = [2 * v for v in convolve(convolve(d, d, args.binomial_order), d, args.binomial_order)]
    require(h == binomial_h, "Literal binomial H check failed")
    q = corrections_stirling(h, args.q_order)
    require(q == corrections_power_series(h, args.q_order), "Independent correction generator check failed")
    a_prefix_count = min(len(a), len(OEIS_A229741))
    c_prefix_count = min(len(c), len(OEIS_A260879))
    require(a[:a_prefix_count] == OEIS_A229741[:a_prefix_count], "Displayed A229741 terms mismatch")
    require(d[:5] == [1, 2, 8, 36, 172], "Initial d terms mismatch")
    require(c[:c_prefix_count] == OEIS_A260879[:c_prefix_count], "Displayed A260879 terms mismatch")
    require(all(c[k + 1] > c[k] for k in range(args.max_index)), "Monotonicity check failed")
    known_q = [[1], [0, 12], [0, 0, 144], [0, 0, 144, 1840],
               [0, 0, 144, 5520, 25008], [0, 0, 144, 12880, 150048, 360304],
               [0, 0, 144, 27600, 625200, 3603040, 5483312]]
    require(q[:7] == known_q, "First six correction polynomials mismatch")
    exact_rows = [{"n": k, "a_n": a[k], "d_n": d[k], "c_n": c[k]}
                  for k in range(args.max_index + 1)]
    write_csv(output / "exact_coefficients.csv", exact_rows)
    write_json(output / "corrections.json", {
        "rho": "log(2)", "h": h[:args.q_order + 1],
        "q_coefficients_ascending_rho_power": q,
        "q_polynomials": [polynomial_string(v) for v in q],
        "independent_power_series_agrees": True})
    ratios = normalized_checks(c, q, sorted(set(args.points)), args.precision)
    # Recompute at higher precision to detect losses hidden by normalization.
    require(ratios == normalized_checks(c, q, sorted(set(args.points)), args.precision + 20),
            "Normalized values changed at 40 displayed decimals under precision increase")
    write_json(output / "normalized_ratios.json", ratios)
    write_csv(output / "normalized_ratios.csv", ratios)
    summary = {"all_exact_checks_passed": True,
               "exact_a_d_c_through": args.max_index,
               "independent_differential_D_through": args.max_index,
               "inverse_signed_Stirling_transform_through": args.max_index,
               "OEIS_A229741_displayed_terms_matched": a_prefix_count,
               "OEIS_A260879_displayed_terms_matched": c_prefix_count,
               "literal_binomial_D_and_H_through": args.binomial_order,
               "independent_correction_polynomials_through": args.q_order,
               "decimal_working_precision": args.precision,
               "displayed_scientific_decimal_places": 40,
               "higher_precision_recheck": args.precision + 20,
               "numerical_points": sorted(set(args.points)),
               "scope": "Exact algebraic checks and numerical illustrations, not certified finite-index asymptotic bounds."}
    write_json(output / "verification.json", summary)
    from render_tables import render_tables
    render_tables(output)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
