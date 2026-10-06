"""Dependency-free deterministic verification CLI for Report 167."""
import sys
sys.dont_write_bytecode = True
import argparse
import json
from fractions import Fraction
from math import comb
from pathlib import Path

from exact_nested import (
    CheckFailure, MAX_N, MAX_POWER_N, MAX_LITERAL_N, check, require_size,
    component_counts, nested_counts, nested_triangle, rational_egf_counts,
    rational_power_triangle, literal_nested_triangle,
)

FIXTURES = Path(__file__).resolve().parent.parent / "data" / "published_fixtures.json"


def read_fixtures(path=FIXTURES):
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    check(data.get("schema") == "report167-published-numeric-fixtures-v1", "fixture schema")
    expected = {"A007838": (0, 23), "A308338": (0, 22), "A392471": (1, 55)}
    for name, (offset, length) in expected.items():
        fixture = data["sequences"][name]
        check(fixture["offset"] == offset, f"fixture offset: {name}")
        terms = fixture["terms"]
        check(len(terms) == length, f"fixture length: {name}")
        check(all(type(v) is str and v.isascii() and v.isdecimal() for v in terms),
              f"fixture term encoding: {name}")
    return data


def _moments(row):
    total = sum(row)
    mean = Fraction(sum(k * value for k, value in enumerate(row)), total)
    variance = Fraction(sum(k * k * value for k, value in enumerate(row)), total) - mean**2
    return {"mean": str(mean), "variance": str(variance)}


def verify(n=MAX_N, power_n=MAX_POWER_N, literal_n=MAX_LITERAL_N,
           include_data=False, fixtures=None):
    require_size(n)
    require_size(power_n, min(n, MAX_POWER_N), "power_n")
    require_size(literal_n, min(n, MAX_LITERAL_N), "literal_n")
    if type(include_data) is not bool:
        raise ValueError("include_data must be bool")
    base = component_counts(n)
    rows = nested_triangle(n)
    scalar = nested_counts(n)
    rational_base, rational_counts = rational_egf_counts(n)
    check(base == rational_base, "cycle product versus rational component recurrence")
    counts = [sum(row) for row in rows]
    check(counts == scalar, "Bell row sums versus scalar least-label recurrence")
    check(counts == rational_counts, "integer counts versus rational EGF recurrence")
    power_rows = rational_power_triangle(power_n)
    check(rows[:power_n + 1] == power_rows, "complete Bell versus power-series triangle")
    literal_rows = literal_nested_triangle(literal_n)
    check(rows[:literal_n + 1] == literal_rows, "complete Bell versus literal cycle grouping")
    check(rows[0] == [1] and base[0] == counts[0] == 1, "empty extensions")
    for size, row in enumerate(rows):
        check(len(row) == size + 1, f"row shape at n={size}")
        check(all(type(v) is int and v >= 0 for v in row), f"nonnegative integer row n={size}")
        if size:
            check(row[0] == 0 and row[1] == base[size] and row[size] == 1,
                  f"boundary columns at n={size}")
            check(all(row[k] > 0 for k in range(1, size + 1)), f"positive interior at n={size}")
        if size >= 2:
            check(row[size - 1] == comb(size, 2), f"next diagonal at n={size}")
            check(counts[size] > counts[size - 1], f"strict count increase at n={size}")
    fixtures = read_fixtures() if fixtures is None else fixtures
    candidates = {
        "A007838": base,
        "A308338": counts,
        "A392471": [rows[size][k] for size in range(1, min(n, 10) + 1)
                     for k in range(1, size + 1)],
    }
    published = {}
    for name, actual in candidates.items():
        fixture = fixtures["sequences"][name]
        ref = [int(value) for value in fixture["terms"]]
        tested = min(len(actual), len(ref))
        check(actual[:tested] == ref[:tested], f"published numeric fixture mismatch: {name}")
        published[name] = {"terms_checked": tested, "available_terms": len(ref),
                           "all_available_checked": tested == len(ref), "equal": True}
    result = {
        "schema": "report167-exact-verification-v1",
        "status": "passed",
        "arithmetic": "integer and fractions.Fraction only",
        "bounds": {"counts_and_integer_triangle": n, "rational_power_triangle": power_n,
                   "literal_permutations_and_cycle_groupings": literal_n},
        "comparisons": {
            "component_coefficients_integer_vs_rational": n + 1,
            "nested_coefficients_integer_vs_rational": n + 1,
            "bell_row_sums_vs_scalar_recurrence": n + 1,
            "complete_triangle_entries_vs_rational_powers": (power_n + 1) * (power_n + 2) // 2,
            "complete_triangle_entries_vs_literal_enumeration": (literal_n + 1) * (literal_n + 2) // 2,
            "complete_integer_triangle_entries": (n + 1) * (n + 2) // 2,
        },
        "published_fixtures": published,
        "exact_moments": {str(j): _moments(rows[j]) for j in (0, 1, 2, 5, 20, 50, 100) if j <= n},
        "scope": "Exact finite equalities only; no certified asymptotic error constants or onset thresholds.",
    }
    if include_data:
        result["data"] = {"base": [str(v) for v in base], "nested": [str(v) for v in counts],
                          "triangle": [[str(v) for v in row] for row in rows]}
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=MAX_N, help="counts and integer triangle, 0..100")
    parser.add_argument("--power-n", type=int, default=None, help="rational power triangle, 0..min(n,30)")
    parser.add_argument("--literal-n", type=int, default=None, help="literal enumeration, 0..min(n,7)")
    parser.add_argument("--include-data", action="store_true", help="include complete exact arrays as decimal strings")
    args = parser.parse_args(argv)
    try:
        result = verify(args.n, min(args.n, MAX_POWER_N) if args.power_n is None else args.power_n,
                        min(args.n, MAX_LITERAL_N) if args.literal_n is None else args.literal_n,
                        args.include_data)
    except (ValueError, TypeError, KeyError, OSError) as error:
        print(json.dumps({"status": "invalid-input", "error": str(error)}, sort_keys=True))
        return 2
    except CheckFailure as error:
        print(json.dumps({"status": "failed", "error": str(error)}, sort_keys=True))
        return 1
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
