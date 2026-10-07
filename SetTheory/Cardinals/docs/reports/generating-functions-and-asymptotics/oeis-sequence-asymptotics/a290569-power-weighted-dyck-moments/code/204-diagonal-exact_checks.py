#!/usr/bin/env python3
"""Finite exact checks for the diagonal weighted-Dyck expansion.

Run ``python exact_checks.py`` to write ``results/exact_checks.json`` next to
this file, or use ``--output-dir DIRECTORY``.  ``run(output_dir)`` returns the
same JSON-serializable result.  All checks raise explicitly, so they remain
active with ``python -O``.  Results contain no machine-dependent data.

The two finite row-box implementations use exact rational arithmetic and
independent exponential-series constructions.  Their formal q parameter is
independent of tau; equality is a finite algebraic identity, not a claim about
an infinite partition sum.  Finite checks supplement, rather than replace,
the mathematical proofs.
"""

import argparse
import json
from fractions import Fraction as F
from math import comb, factorial, prod
from pathlib import Path

import sympy as s
from sympy.functions.combinatorial.numbers import stirling


DIAGONAL_INITIAL_TERMS = [
    1,
    1,
    5,
    297,
    485729,
    38103228225,
    220579355255364545,
    134210828762693919568092033,
    11583583466188874003924403353591815169,
    183988806081826466732185672966967145613350641690625,
    676960735217941793634104089611911809588055950029181968418342810625,
]


def parts(m, cap=None):
    """Generate partitions of m as nonincreasing tuples of positive parts."""
    if m == 0:
        yield ()
        return
    if cap is None:
        cap = m
    for j in range(min(m, cap), 0, -1):
        for tail in parts(m - j, j):
            yield (j,) + tail


def conjugate(lam):
    return tuple(sum(x >= j for x in lam) for j in range(1, lam[0] + 1)) if lam else ()


def D(lam, k):
    """D_k in zero-based row indexing, evaluated over the rationals."""
    return sum((F((i + x) ** k - i ** k, k) for i, x in enumerate(lam)), F(0))


def paths(n, u=0, d=0, heights=(), up_counts=()):
    """Enumerate Dyck paths, recording descent heights and preceding upsteps."""
    if d == n:
        yield heights, up_counts
        return
    if u < n:
        yield from paths(n, u + 1, d, heights, up_counts)
    if d < u:
        yield from paths(n, u, d + 1, heights + (u - d,), up_counts + (u,))


def walk_dp(n, p):
    """Integer height-transfer computation of the sum of descent weights."""
    old = {0: 1}
    for k in range(2 * n):
        new = {}
        for h, w in old.items():
            if h + 1 <= 2 * n - k - 1:
                new[h + 1] = new.get(h + 1, 0) + w
            if h:
                new[h - 1] = new.get(h - 1, 0) + w * h**p
        old = new
    return old.get(0, 0)


def sf_coeff(n, p):
    """Coefficient of x^n from a depth-n formal Stieltjes fraction."""
    f = [1] + [0] * n
    for h in range(n, 0, -1):
        b = [1] + [0] * n
        for k in range(1, n + 1):
            b[k] = h**p * sum(f[j] * b[k - 1 - j] for j in range(k))
        f = b
    return f[n]


def coeff(lam, tau, sigma, order):
    """Exponential coefficients via the derivative coefficient recurrence."""
    a = [F(0)] + [tau * D(lam, r + 1) + sigma * D(lam, r)
                  for r in range(1, order + 1)]
    b = [F(1)]
    for r in range(1, order + 1):
        b.append(-sum(j * a[j] * b[r - j] for j in range(1, r + 1)) / r)
    return b


def mul(x, y, order):
    return [sum(x[i] * y[r - i] for i in range(r + 1))
            for r in range(order + 1)]


def box_enumerate(size, cap=None, prefix=()):
    """Enumerate every partition in a size-by-size square exactly once."""
    if cap is None:
        cap = size
    yield prefix
    if len(prefix) == size:
        return
    for j in range(1, cap + 1):
        yield from box_enumerate(size, j, prefix + (j,))


def box_dp(size, q, tau, sigma, order):
    """Exact row-box DP using a product of elementary exponential series."""
    nxt = [[F(1)] + [F(0)] * order for _ in range(size + 1)]
    for i in range(size, 0, -1):
        row = [[F(1)] + [F(0)] * order]
        for j in range(1, size + 1):
            a = [F(0)] + [
                tau * F((i - 1 + j) ** (r + 1) - (i - 1) ** (r + 1), r + 1)
                + sigma * F((i - 1 + j) ** r - (i - 1) ** r, r)
                for r in range(1, order + 1)
            ]
            w = [F(1)] + [F(0)] * order
            for r in range(1, order + 1):
                factor = [F(0)] * (order + 1)
                for ell in range(order // r + 1):
                    factor[r * ell] = (-a[r]) ** ell / factorial(ell)
                w = mul(w, factor, order)
            ww = mul(w, nxt[j], order)
            row.append([row[j - 1][r] + q**j * ww[r] for r in range(order + 1)])
        nxt = row
    return nxt[size]


def exact_threshold(y, diagonal_terms):
    """Find N(y) = min{n >= 1: a_n >= y} within a supplied exact prefix."""
    if not isinstance(y, int) or y <= 1:
        raise ValueError("The threshold input must be an integer greater than 1")
    for n in range(1, len(diagonal_terms)):
        if diagonal_terms[n] >= y:
            return n
    raise ValueError("The supplied exact diagonal prefix does not reach the threshold")


def run(output_dir):
    """Run the finite checks and write deterministic exact_checks.json."""
    checks = 0

    def need(ok, label):
        nonlocal checks
        checks += 1
        if not ok:
            raise RuntimeError("Exact check failed: " + label)

    path_count = 0
    grid_count = 0
    diagonal = []
    for n in range(11):
        seen = set()
        totals = [0] * 7
        diagonal_total = 0
        for heights, up_counts in paths(n):
            lam = tuple(n - v for v in up_counts if n - v)
            need(lam not in seen, f"path/partition injectivity at n={n}")
            seen.add(lam)
            need(all(x <= n - i - 1 for i, x in enumerate(lam)), "staircase bounds")
            padded = lam + (0,) * (n - len(lam))
            need(tuple(n - i - x for i, x in enumerate(padded)) == heights, "descent heights")
            row_product = prod((F(n - i - x, n - i) for i, x in enumerate(lam)), start=F(1))
            cell_product = prod((F(n - i - j, n - i - j + 1)
                                 for i, x in enumerate(lam) for j in range(1, x + 1)), start=F(1))
            need(row_product == cell_product == F(prod(heights), factorial(n)), "row/cell telescoping")
            need(max((i + x for i, x in enumerate(lam)), default=0) <= n - 1 or n == 0,
                 "row singularity radius")
            base = prod(heights)
            for p in range(7):
                totals[p] += base**p
            diagonal_total += base**n
            path_count += 1
        need(len(seen) == comb(2 * n, n) // (n + 1), "Catalan count")
        for p, total in enumerate(totals):
            need(total == walk_dp(n, p) == sf_coeff(n, p), "three exact constructions")
            grid_count += 1
        need(diagonal_total == walk_dp(n, n) == sf_coeff(n, n), "three diagonal constructions")
        diagonal.append(diagonal_total)
    need(diagonal == DIAGONAL_INITIAL_TERMS, "diagonal initial values n=0..10")

    # One extra exact term supplies the upper endpoint for y=a_10+1.
    guard = walk_dp(11, 11)
    need(guard == sf_coeff(11, 11), "exact upper guard at n=11")
    guarded_diagonal = diagonal + [guard]
    need(all(guarded_diagonal[n + 1] > guarded_diagonal[n] for n in range(1, 11)),
         "strict growth on the checked positive-index prefix")
    threshold_samples = []
    for n in range(2, 11):
        for offset in (-1, 0, 1):
            y = diagonal[n] + offset
            expected = n + (offset == 1)
            actual = exact_threshold(y, guarded_diagonal)
            need(actual == expected, "exact integer threshold near a_" + str(n))
            need(guarded_diagonal[actual - 1] < y <= guarded_diagonal[actual],
                 "exact threshold bracketing")
            threshold_samples.append({"center_index": n, "offset": offset, "Y": y, "N": actual})
    need(exact_threshold(2, guarded_diagonal) == 2, "first nontrivial integer threshold")

    partition_count = 0
    for m in range(19):
        for lam in parts(m):
            conj = conjugate(lam)
            for k in range(1, 8):
                value = D(lam, k)
                cell = sum((F((i + j) ** k - (i + j - 1) ** k, k)
                            for i, x in enumerate(lam) for j in range(1, x + 1)), F(0))
                need(value == cell == D(conj, k), "D row/cell/conjugation")
                need(0 <= value <= m**k, "D bound")
            need(D(lam, 2) == sum(i * x for i, x in enumerate(lam))
                 + sum(i * x for i, x in enumerate(conj)) + F(m, 2), "D2 statistic identity")
            if m >= 2:
                need(D(lam, 2) >= 2, "TV sign classification")
            for n in (m + 1, m + 2):
                need(all(x <= n - i - 1 for i, x in enumerate(lam)), "small-size staircase inclusion")
            partition_count += 1

    box_count = 0
    parameters = [(F(1, 3), F(1), F(0)),
                  (F(2, 5), F(3, 2), F(-2, 3)),
                  (F(1, 4), F(1, 2), F(3, 5))]
    for size in range(7):
        for q, tau, sigma in parameters:
            expected = [F(0)] * 5
            for lam in box_enumerate(size):
                b = coeff(lam, tau, sigma, 4)
                expected = [x + q**sum(lam) * y for x, y in zip(expected, b)]
            need(box_dp(size, q, tau, sigma, 4) == expected, "rational row-box coefficient equality")
            box_count += 1

    # General coefficient identities B_0 through B_4.
    z = s.symbols("z")
    aa = s.symbols("a1:5")
    poly = s.Poly(s.series(s.exp(-sum(aa[j - 1] * z**j for j in range(1, 5))), z, 0, 5).removeO(), z)
    shown = [1, -aa[0], aa[0] ** 2 / 2 - aa[1],
             -aa[2] + aa[0] * aa[1] - aa[0] ** 3 / 6,
             -aa[3] + aa[0] * aa[2] + aa[1] ** 2 / 2
             - aa[0] ** 2 * aa[1] / 2 + aa[0] ** 4 / 24]
    for r in range(5):
        need(s.expand(poly.nth(r) - shown[r]) == 0, "B" + str(r))

    # Multiplicity increments close in weighted degree, with a fixed part label j.
    S, M, j, t = s.symbols("S M j t", integer=True, nonnegative=True)
    for k in range(1, 8):
        increment = s.expand(s.summation(s.expand(((S + t + j) ** k - (S + t) ** k)
                                                  / s.Integer(k)), (t, 0, M - 1)))
        need(s.Poly(increment, S, M).total_degree() <= k, "multiplicity weighted-degree closure")
    q = s.symbols("q")
    moment = s.Integer(1)
    for r in range(1, 9):
        moment = s.factor((1 - q) * q * s.diff(moment / (1 - q), q))
        stirling_moment = sum(stirling(r, ell, kind=2) * factorial(ell)
                              * (q / (1 - q)) ** ell for ell in range(r + 1))
        need(s.cancel(moment - stirling_moment) == 0, "geometric raw moment")

    # Inverse residual from derivatives of the elementary leading terms.
    u, c, d, e1 = s.symbols("u c d e1")
    H = 2 * u - 1
    A = (u + c) / 2
    a0 = -A / H
    a1 = -((H + 2) * a0 * a0 / 2 + (A + s.Rational(1, 2)) * a0 + d) / H
    a2 = -((H + 2) * a0 * a1 + a0**3 / 3 + (A + s.Rational(1, 2)) * a1
           + a0 * a0 / 4 + e1) / H
    v0, v1, v2 = s.symbols("v0 v1 v2")
    v = v0 + v1 * z + v2 * z * z
    residual = s.Poly(s.expand(H * v + A
                              + z * ((H + 2) * v * v / 2 + (A + s.Rational(1, 2)) * v + d)
                              + z * z * (v**3 / 3 + v * v / 4 + e1)), z)
    for r in range(3):
        need(s.cancel(residual.nth(r).subs({v0: a0, v1: a1, v2: a2})) == 0,
             "inverse alpha residual " + str(r))

    # Triangular inverse recurrence through alpha_6, without nested substitution.
    vv = s.symbols("v0:7")
    bb = s.symbols("b1:6")
    v = sum(vv[i] * z**i for i in range(7))
    log_series = sum((-1) ** (k + 1) * (z * v) ** k / s.Integer(k) for k in range(1, 9))
    expression = ((1 + z * v) ** 2 * (u - 1 + log_series) - (u - 1)) / z
    expression += (1 + z * v) * (u + c + log_series) / 2 + d * z
    expression += sum(bb[r - 1] * z ** (r + 1)
                      * sum((-1) ** k * s.binomial(r + k - 1, k) * (z * v) ** k
                            for k in range(7 - r)) for r in range(1, 6))
    psi = s.series(expression, z, 0, 7).removeO().expand()
    for r in range(7):
        pc = psi.coeff(z, r)
        need(s.expand(s.diff(pc, vv[r]) - H) == 0, "inverse triangular diagonal")
        need(not any(vv[k] in pc.free_symbols for k in range(r + 1, 7)), "inverse triangular dependence")
        need(not any(bb[k - 1] in pc.free_symbols for k in range(max(1, r), 6)), "inverse coefficient index")

    # Rational endpoint values used with the positive-power-series TV bounds.
    q = F(3, 8)
    mu_upper = q / (2 * (1 - q)) + (q * (1 + q) / (1 - q) ** 3
                                   - q / (2 * (1 - q) ** 2) - q / 2) / (1 - q * q)
    need(mu_upper == F(27237, 13750) < 2, "TV upper rational endpoint")
    q = F(1, 3)
    mu_lower = q / (2 * (1 - q)) + 3 * q * q / (1 - q * q)
    need(mu_lower == F(5, 8) > F(1, 2), "TV lower rational endpoint")

    result = {
        "status": "PASS",
        "explicit_checks": checks,
        "dyck_paths_enumerated": path_count,
        "exact_three_way_grid_comparisons": grid_count,
        "exact_three_way_diagonal_comparisons": len(diagonal),
        "exact_diagonal_terms_n0_to10": diagonal,
        "integer_threshold_definition": "N(Y) = min{n >= 1: a_n >= Y}, Y > 1",
        "integer_threshold_boundary_cases": threshold_samples,
        "integer_threshold_at_2": 2,
        "integer_threshold_upper_guard_n11": guard,
        "unrestricted_partitions_checked_m0_to18": partition_count,
        "rational_row_box_checks": box_count,
        "row_box_sizes": "0..6",
        "row_box_coefficient_orders": "0..4",
        "symbolic_B_orders": "0..4",
        "multiplicity_update_degrees": "1..7",
        "geometric_moment_orders": "1..8",
        "inverse_explicit_residual_orders": "0..2",
        "inverse_triangular_orders": "0..6",
        "TV_mu_lower": str(mu_lower),
        "TV_mu_upper": str(mu_upper),
    }
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / "exact_checks.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent / "results")
    args = parser.parse_args()
    print(json.dumps(run(args.output_dir), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
