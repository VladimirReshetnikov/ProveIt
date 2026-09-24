#!/usr/bin/env python3
"""Exact checks for canonical binomial decomposition and its counterexamples.

Requires Python 3.10+ and only the standard library.  Run from any directory:
    python verify.py
    python verify.py --family-limit 10000

All decisions about real roots in degrees at most three use integer
polynomial discriminants.  Higher-degree certificates use an exact necessary
Newton inequality.  No numerical root finder or floating-point arithmetic is
used.  The infinite-family conclusions additionally require the proofs in
article.tex; finite computation alone does not establish those conclusions.
"""
from __future__ import annotations

import argparse
import csv
import json
from collections import Counter
from fractions import Fraction
from math import comb
from pathlib import Path
from typing import Iterable, Sequence


def require(condition: bool, message: str) -> None:
    """A check which remains enabled under python -O."""
    if not condition:
        raise AssertionError(message)


def binomial_expansion(value: int, order: int) -> list[tuple[int, int]]:
    """The unique greedy order-binomial expansion of a nonnegative integer.

    Return (upper, lower) pairs in strictly decreasing lower order.  Zero has
    the empty expansion.  Integer binary search is exact even for huge values.
    """
    if type(value) is not int or value < 0:
        raise ValueError("value must be a nonnegative integer")
    if type(order) is not int or order < 1:
        raise ValueError("order must be a positive integer")
    remainder, lower = value, order
    terms: list[tuple[int, int]] = []
    while remainder:
        require(lower >= 1, "greedy algorithm exhausted all lower indices")
        if lower == 1:
            upper = remainder
        else:
            lo, hi = lower - 1, lower
            while comb(hi, lower) <= remainder:
                hi *= 2
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if comb(mid, lower) <= remainder:
                    lo = mid
                else:
                    hi = mid
            upper = lo
        terms.append((upper, lower))
        remainder -= comb(upper, lower)
        lower -= 1
    return terms


def expansion_reference(value: int, order: int) -> list[tuple[int, int]]:
    """Independent slow linear-search implementation, used only in tests."""
    terms: list[tuple[int, int]] = []
    for lower in range(order, 0, -1):
        if value == 0:
            break
        if lower == 1:
            upper = value
        else:
            upper = lower
            while comb(upper + 1, lower) <= value:
                upper += 1
        terms.append((upper, lower))
        value -= comb(upper, lower)
    require(value == 0, "reference algorithm did not terminate")
    return terms


def split_integer(value: int, order: int) -> tuple[int, int]:
    """Return (R_order(value), K_order(value))."""
    terms = binomial_expansion(value, order)
    r = sum(comb(a - 1, k) for a, k in terms)
    h = sum(comb(a - 1, k - 1) for a, k in terms)
    require(r + h == value, "Pascal splitting identity failed")
    return r, h


def decompose(coefficients: Sequence[int]) -> tuple[list[int], list[int]]:
    """Ascending coefficient lists; preserve trailing zeros in G."""
    if not coefficients or coefficients[0] != 1:
        raise ValueError("input must have constant coefficient one")
    if any(type(c) is not int or c <= 0 for c in coefficients):
        raise ValueError("all input coefficients must be positive integers")
    g, h = [1], []
    for k, coefficient in enumerate(coefficients[1:], start=1):
        r, kap = split_integer(coefficient, k)
        g.append(r)
        h.append(kap)
    require(all(coefficients[k] == g[k] + h[k - 1]
                for k in range(1, len(coefficients))), "F != G + tH")
    return g, h


def product(slopes: Iterable[int]) -> list[int]:
    coefficients = [1]
    for slope in slopes:
        if type(slope) is not int or slope <= 0:
            raise ValueError("slopes must be positive integers")
        result = [0] * (len(coefficients) + 1)
        for i, coefficient in enumerate(coefficients):
            result[i] += coefficient
            result[i + 1] += slope * coefficient
        coefficients = result
    return coefficients


def cubic_discriminant(a: int, b: int, c: int) -> int:
    """Discriminant of 1 + a*t + b*t**2 + c*t**3 (c may be zero)."""
    return a*a*b*b - 4*b*b*b - 4*a*a*a*c - 27*c*c + 18*a*b*c


def trimmed(coefficients: Sequence[int]) -> list[int]:
    values = list(coefficients)
    while len(values) > 1 and values[-1] == 0:
        values.pop()
    return values


def all_real_small(coefficients: Sequence[int]) -> bool:
    """Exact real-rootedness decision for degree at most three, constant 1."""
    values = trimmed(coefficients)
    if not values or values[0] != 1:
        raise ValueError("constant coefficient must be one")
    if len(values) <= 2:
        return True
    if len(values) == 3:
        return values[1]**2 - 4*values[2] >= 0
    if len(values) == 4:
        return cubic_discriminant(*values[1:]) >= 0
    raise ValueError("only degrees zero through three are supported")


def check_expansions() -> int:
    count = 0
    for order in range(1, 9):
        for value in range(2049):
            terms = binomial_expansion(value, order)
            require(terms == expansion_reference(value, order),
                    f"independent expansion mismatch at {(value, order)}")
            require(sum(comb(a, k) for a, k in terms) == value,
                    "expansion does not sum to input")
            require(all(a >= k >= 1 for a, k in terms), "invalid term")
            require(all(terms[i][0] > terms[i+1][0] and
                        terms[i][1] == terms[i+1][1] + 1
                        for i in range(len(terms)-1)), "ordering failed")
            split_integer(value, order)
            count += 1
        # Additional boundary tests beyond the small exhaustive range.
        for upper in range(max(order, 2), 201):
            for delta in (-1, 0, 1):
                value = comb(upper, order) + delta
                if value >= 0:
                    terms = binomial_expansion(value, order)
                    require(terms == expansion_reference(value, order),
                            f"boundary mismatch at {(value, order)}")
                    split_integer(value, order)
                    count += 1
    # Invalid inputs must fail rather than be silently truncated/coerced.
    for value, order in [(-1, 2), (1, 0), (1.5, 2), (True, 1)]:
        try:
            binomial_expansion(value, order)  # type: ignore[arg-type]
        except ValueError:
            pass
        else:
            raise AssertionError("invalid input was accepted")
    return count


def check_main_examples() -> dict[str, object]:
    f = product([2, 3, 3])
    g, h = decompose(f)
    require(f == [1, 8, 21, 18], "main input mismatch")
    require(g == [1, 7, 15, 8] and h == [1, 6, 10], "main split mismatch")
    require(binomial_expansion(18, 3) == [(5, 3), (4, 2), (2, 1)],
            "18 has the wrong canonical expansion")
    require(cubic_discriminant(*g[1:]) == -59, "main G discriminant")
    require(h[1]**2 - 4*h[2] == -4, "main H discriminant")
    require(all_real_small(f) and not all_real_small(g)
            and not all_real_small(h), "main root classification")
    f2 = product([2, 3, 4])
    g2, h2 = decompose(f2)
    require(f2 == [1, 9, 26, 24], "simple-root input mismatch")
    require(g2 == [1, 8, 19, 11] and h2 == [1, 7, 13], "simple split")
    require(cubic_discriminant(*f2[1:]) == 4, "simple input discriminant")
    require(cubic_discriminant(*g2[1:]) == -31, "simple G discriminant")
    require(h2[1]**2 - 4*h2[2] == -3, "simple H discriminant")
    return {"main": {"F": f, "G": g, "H": h,
                     "G_discriminant": -59, "H_discriminant": -4},
            "simple_roots": {"F": f2, "G": g2, "H": h2,
                             "G_discriminant": -31, "H_discriminant": -3}}


def cubic_search() -> tuple[list[dict[str, object]], dict[str, object]]:
    rows: list[dict[str, object]] = []
    tested = 0
    for a in range(3, 9):
        for b in range(3, a*a // 3 + 1):
            for c in range(1, a*a*a // 27 + 1):
                tested += 1
                disc = cubic_discriminant(a, b, c)
                if disc < 0:
                    continue
                g, h = decompose([1, a, b, c])
                rows.append({"a": a, "b": b, "c": c,
                             "F_discriminant": disc,
                             "g1": g[1], "g2": g[2], "g3": g[3],
                             "h1": h[1], "h2": h[2],
                             "G_discriminant_formula": cubic_discriminant(*g[1:]),
                             "H_discriminant": h[1]**2 - 4*h[2],
                             "G_all_real": all_real_small(g),
                             "H_all_real": all_real_small(h)})
    counts = Counter(int(row["a"]) for row in rows)
    require(dict(counts) == {3: 1, 4: 2, 5: 6, 6: 16, 7: 33, 8: 66},
            f"unexpected cubic counts: {counts}")
    failures = [row for row in rows if not row["G_all_real"]
                or not row["H_all_real"]]
    require([(row["a"], row["b"], row["c"]) for row in failures]
            == [(8, 21, 18)], "unexpected minimal cubic counterexamples")
    return rows, {"candidates_tested": tested,
                  "real_rooted_inputs": len(rows),
                  "real_rooted_by_linear_coefficient": dict(counts),
                  "counterexamples": [[8, 21, 18]],
                  "scope": "cubics with positive integer coefficients and a <= 8"}


def family_rows(limit: int, slopes: tuple[int, int, int]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for m in range(1, limit + 1):
        f = product(m*a for a in slopes)
        g, h = decompose(f)
        rows.append({"m": m, "u": h[1], "v": h[2],
                     "g1": g[1], "g2": g[2], "g3": g[3],
                     "H_discriminant": h[1]**2 - 4*h[2],
                     "G_discriminant_formula": cubic_discriminant(*g[1:]),
                     "G_degree": len(trimmed(g)) - 1,
                     "G_all_real": all_real_small(g),
                     "H_all_real": all_real_small(h)})
    return rows


def check_tail_constants() -> None:
    # rho=6^(1/3); rho^2>33/10; rho<11/6; sqrt(6)<5/2.
    require(Fraction(33, 10)**3 < 36, "repeated rho lower bound")
    require(Fraction(11, 6)**3 > 6, "repeated rho upper bound")
    require(Fraction(5, 2)**2 > 6, "repeated sqrt bound")
    q = lambda m: -Fraction(3, 5)*m*m + 16*m - 3
    require(q(27) < 0 and q(28) - q(27) < 0, "repeated tail")
    # For q(m) with negative quadratic coefficient its forward differences
    # decrease, so the preceding two checks prove q(m)<0 for every m>=27.
    # rho=144^(1/3); rho^2>137/5; rho<21/4; sqrt(52)<29/4.
    require(Fraction(137, 5)**3 < 144**2, "simple rho lower bound")
    require(Fraction(21, 4)**3 > 144, "simple rho upper bound")
    require(Fraction(29, 4)**2 > 52, "simple sqrt bound")
    q2 = lambda m: -Fraction(14, 5)*m*m + 46*m - 3
    require(q2(17) < 0 and q2(18) - q2(17) < 0, "simple tail")


def higher_degree_examples() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for degree in range(3, 21):
        m = 1
        for attempt in range(31):
            _, h = decompose([comb(degree, k)*m**k for k in range(degree + 1)])
            # H has degree n=degree-1, with constant one.  Real-rootedness
            # requires (n-1)*h1^2 >= 2*n*h2.
            defect = (degree - 2)*h[1]**2 - 2*(degree - 1)*h[2]
            if defect < 0:
                rows.append({"degree": degree, "m": m,
                             "h1": h[1], "h2": h[2],
                             "first_Newton_defect": defect})
                break
            m *= 2
        else:
            raise AssertionError(f"no certificate found for degree {degree}")
    return rows


def write_csv(path: Path, rows: Sequence[dict[str, object]]) -> None:
    require(bool(rows), f"no data for {path.name}")
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def write_latex_tables(directory: Path, repeated: Sequence[dict[str, object]],
                       simple: Sequence[dict[str, object]],
                       higher: Sequence[dict[str, object]]) -> None:
    # Small tables needed by the article.  The complete extended calculations
    # are in CSV, not in an unwieldy printed appendix.
    with (directory / "repeated_table.tex").open("w", encoding="utf-8") as out:
        for row in repeated[:26]:
            out.write("{m} & {u} & {v} & {H_discriminant} & "
                      "{G_discriminant_formula} \\\\\n".format(**row))
    with (directory / "simple_table.tex").open("w", encoding="utf-8") as out:
        for row in simple[:16]:
            out.write("{m} & {u} & {v} & {H_discriminant} \\\\\n".format(**row))
    with (directory / "higher_degree_table.tex").open("w", encoding="utf-8") as out:
        for row in higher:
            out.write("{degree} & {m} & {h1} & {h2} & "
                      "{first_Newton_defect} \\\\\n".format(**row))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family-limit", type=int, default=1000,
                        help="finite extra checks for each cubic family (>=27)")
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent,
                        help="directory for regenerated tables and report")
    args = parser.parse_args()
    if args.family_limit < 27:
        parser.error("--family-limit must be at least 27")
    output = args.output_dir.resolve()
    data = output / "data"
    data.mkdir(parents=True, exist_ok=True)
    count = check_expansions()
    main_examples = check_main_examples()
    cubic_rows, cubic_summary = cubic_search()
    repeated = family_rows(args.family_limit, (1, 1, 1))
    simple = family_rows(args.family_limit, (2, 3, 4))
    require([r["m"] for r in repeated if r["H_all_real"]] == [1, 2, 4, 6],
            "repeated H classification failed in checked range")
    require([r["m"] for r in repeated if r["G_all_real"]] == [1, 2, 6],
            "repeated G classification failed in checked range")
    require([r["m"] for r in simple if r["H_all_real"]] == [3, 4],
            "simple H classification failed in checked range")
    check_tail_constants()
    higher = higher_degree_examples()
    # Finite checks of the uniform all-degree theorem, not a substitute for it.
    uniform_checks = []
    for degree in range(3, 201):
        m = 20*(degree - 1)
        u = split_integer(comb(degree, 2)*m*m, 2)[1]
        v = split_integer(comb(degree, 3)*m*m*m, 3)[1]
        defect = (degree - 2)*u*u - 2*(degree - 1)*v
        require(defect < 0, f"uniform threshold failed at d={degree}")
        uniform_checks.append(degree)
    write_csv(data / "cubics_a_le8.csv", cubic_rows)
    write_csv(data / "repeated_cubic_family.csv", repeated)
    write_csv(data / "simple_cubic_family.csv", simple)
    write_csv(data / "higher_degree_certificates.csv", higher)
    write_latex_tables(data, repeated, simple, higher)
    report = {"status": "ALL EXACT CHECKS PASSED",
              "arithmetic": "Python arbitrary-precision integers and rational fractions",
              "expansion_cross_checks": count,
              "examples": main_examples,
              "minimal_cubic_search": cubic_summary,
              "repeated_family": {"checked_through_m": args.family_limit,
                                  "H_real_rooted_m": [1, 2, 4, 6],
                                  "G_real_rooted_m": [1, 2, 6],
                                  "analytic_H_tail_begins_at": 27},
              "simple_family": {"checked_through_m": args.family_limit,
                                "H_real_rooted_m": [3, 4],
                                "analytic_H_tail_begins_at": 17},
              "higher_degree_certificates": higher,
              "uniform_threshold_checks": {"m": "20*(d-1)",
                                           "degrees_checked": [3, 200],
                                           "number_checked": len(uniform_checks)},
              "scope_note": "Infinite results use the analytic proofs in article.tex; "
                            "finite ranges are not treated as infinite proofs.",
              "formalization_note": "Not a proof-assistant formalization."}
    with (output / "verification_report.json").open("w", encoding="utf-8") as out:
        json.dump(report, out, indent=2)
        out.write("\n")
    print(report["status"])
    print(f"Independent binomial-expansion comparisons: {count}")
    print(f"Cubic candidates: {cubic_summary['candidates_tested']}; "
          f"real-rooted inputs: {cubic_summary['real_rooted_inputs']}")
    print("Unique cubic failure with a<=8: (a,b,c)=(8,21,18)")
    print(f"Both cubic families checked through m={args.family_limit}")
    print("Rational inequalities establishing the analytic tails passed")
    print("Higher-degree integer Newton certificates written for d=3,...,20")
    print("Uniform threshold m=20*(d-1) checked for d=3,...,200")
    print(f"Artifacts written to {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
