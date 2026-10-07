#!/usr/bin/env python3
"""Optional 55/75-digit OEIS replay; floating evaluation is not interval-certified.

Quick: python optional/replay_oeis.py
Full:  python optional/replay_oeis.py --full
Needs mpmath. Nothing is written unless --output PATH is supplied.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "code"))


def run(count, precisions):
    import mpmath as mp
    from positive_tail import tail_bound

    fixture = json.loads((ROOT / "data" / "oeis_prefix.json").read_text(encoding="utf-8"))
    expected = fixture["values"]
    if len(expected) != 35 or fixture["offset"] != 0:
        raise ValueError("The fixture must contain the 35 recorded values at indices 0..34")
    if any(type(n) is not int or n < 0 for n in expected):
        raise ValueError("Every fixture value must be a nonnegative integer")
    rows = []
    for n, target in enumerate(expected[:count]):
        cutoff = 4 * n + 60 if n else 0
        bound = tail_bound(n, cutoff) if n else Fraction(0)
        if not isinstance(bound, Fraction) or bound < 0:
            raise ValueError("tail_bound must return a nonnegative Fraction")
        rows.append({"n": n, "expected_integer": target, "sqrt_cutoff_T": cutoff,
                     "last_summed_index": cutoff * cutoff,
                     "exact_positive_tail_bound": str(bound),
                     "tail_below_1e_minus_35": bound < Fraction(1, 10 ** 35),
                     "evaluations": []})

    # The factors depend on k and precision, but not n. Cache them once per
    # precision. This changes no summation terms and makes the full run faster.
    max_index = max(row["last_summed_index"] for row in rows)
    for digits in precisions:
        with mp.workdps(digits):
            roots = [mp.sqrt(k) for k in range(max_index + 1)]
            reciprocal_gamma = [mp.rgamma(1 + root) for root in roots]
            for row in rows:
                n = row["n"]
                if n == 0:
                    value = mp.mpf(1)
                else:
                    log_n = mp.log(n)
                    value = mp.fsum(mp.exp(roots[k] * log_n) * reciprocal_gamma[k]
                                    for k in range(row["last_summed_index"] + 1))
                bound = Fraction(row["exact_positive_tail_bound"])
                floating_bound = mp.mpf(bound.numerator) / bound.denominator
                target = row["expected_integer"]
                row["evaluations"].append({
                    "decimal_digits": digits,
                    "finite_sum": mp.nstr(value, digits),
                    "floor": int(mp.floor(value)),
                    "floor_after_adding_tail_bound_diagnostic": int(mp.floor(value + floating_bound)),
                    "distance_to_nearest_target_floor_boundary_diagnostic":
                        mp.nstr(min(value - target, target + 1 - value), 18),
                })

    for row in rows:
        row["diagnostic_pass"] = row["tail_below_1e_minus_35"] and all(
            evaluation["floor"] == row["expected_integer"] and
            evaluation["floor_after_adding_tail_bound_diagnostic"] == row["expected_integer"]
            for evaluation in row["evaluations"])
    return {"kind": "oeis_prefix_floating_replay", "sequence": fixture["sequence"],
            "source_url": fixture["source_url"], "source_access_date": fixture["access_date"],
            "indices": [0, count - 1], "decimal_precisions": precisions,
            "mpmath_version": mp.__version__,
            "interval_certified": False,
            "qualification": "The positive truncation bound is exact rational arithmetic. "
                             "The finite sums, floors, and margins use floating arithmetic; "
                             "agreement at two precisions is a diagnostic, not a rounding certificate.",
            "all_diagnostic_checks_pass": all(row["diagnostic_pass"] for row in rows),
            "rows": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--count", type=int, default=3, help="Prefix length, 1..35 (default: 3)")
    parser.add_argument("--full", action="store_true", help="Replay all 35 recorded values")
    parser.add_argument("--precisions", type=int, nargs=2, default=[55, 75], metavar=("LOW", "HIGH"))
    parser.add_argument("--output", type=Path, help="Also write JSON to this explicit path")
    args = parser.parse_args()
    try:
        count = 35 if args.full else args.count
        if not 1 <= count <= 35:
            raise ValueError("--count must lie in 1..35")
        if not 30 <= args.precisions[0] < args.precisions[1] <= 300:
            raise ValueError("Use two increasing decimal precisions between 30 and 300")
        result = run(count, args.precisions)
        rendered = json.dumps(result, indent=2) + "\n"
        if args.output is not None:
            args.output.write_text(rendered, encoding="utf-8")
        print(rendered, end="")
        return 0 if result["all_diagnostic_checks_pass"] else 1
    except (ImportError, OSError, ValueError, ArithmeticError) as exc:
        print(json.dumps({"status": "error", "message": str(exc), "interval_certified": False}))
        return 2


if __name__ == "__main__":
    sys.exit(main())
