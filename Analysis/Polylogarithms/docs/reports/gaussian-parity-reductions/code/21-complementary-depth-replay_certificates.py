"""Replay stored finite certificates using only the Python standard library.

This checks exact coefficients, formal shuffle expansions, rational matrix
ranks, the S4 dual witness, and stored interval widths. It does not replace
the article's analytic proof or regenerate the interval tail estimates;
run certify_gaussian.py for the latter.
"""
from __future__ import annotations
from fractions import Fraction
from pathlib import Path
import json
import sys

from polylog_words import complement_reduce, one_zero_formula, shuffle_many

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(100000)
ROOT = Path(__file__).resolve().parents[1]


def load(name: str):
    return json.loads((ROOT / "certificates" / name).read_text())


def rank(rows: list[list[int]]) -> int:
    """Exact rational Gaussian elimination; does not trust a stored rank."""
    if not rows:
        return 0
    width = len(rows[0])
    if any(len(row) != width for row in rows):
        raise ValueError("Ragged matrix.")
    a = [[Fraction(x) for x in row] for row in rows]
    pivot_row = 0
    for col in range(width):
        candidates = [j for j in range(pivot_row, len(a)) if a[j][col]]
        if not candidates:
            continue
        j = candidates[0]
        a[pivot_row], a[j] = a[j], a[pivot_row]
        pivot = a[pivot_row][col]
        a[pivot_row] = [x / pivot for x in a[pivot_row]]
        for j in range(pivot_row + 1, len(a)):
            factor = a[j][col]
            if factor:
                a[j] = [x - factor * y for x, y in zip(a[j], a[pivot_row])]
        pivot_row += 1
        if pivot_row == len(a):
            break
    return pivot_row


def decode_terms(entries):
    result = {}
    for t in entries:
        key = (t["log_power"], tuple(t["q_indices"]), tuple(t["zeta_indices"]))
        if key in result or t["denominator"] <= 0 or t["numerator"] == 0:
            raise ValueError("Noncanonical stored reduction term.")
        result[key] = Fraction(t["numerator"], t["denominator"])
    return result


def read_interval(record):
    lo = Fraction(int(record["lower_numerator"]), int(record["lower_denominator"]))
    hi = Fraction(int(record["upper_numerator"]), int(record["upper_denominator"]))
    assert lo <= hi
    return lo, hi


def main() -> None:
    catalogue = load("complementary_depth_catalogue.json")
    for entry in catalogue:
        word = tuple(map(int, entry["word"]))
        assert len(word) == entry["weight"] and sum(word) == entry["depth"]
        assert decode_terms(entry["terms"]) == complement_reduce(word)
    for entry in load("one_zero.json"):
        assert decode_terms(entry["terms"]) == one_zero_formula(entry["a"], entry["b"])
    triples = load("weight6_triples_shuffle.json")
    columns = [entry["word"] for entry in triples]
    rows = []
    for entry in triples:
        factors = [tuple(map(int, f)) for f in entry["factors"]]
        actual = {"".join(map(str, word)): c for word, c in shuffle_many(factors).items()}
        stored = {t["word"]: t["coefficient"] for t in entry["expansion"]}
        assert actual == stored
        if not entry["lyndon"]:
            rows.append([stored.get(word, 0) for word in columns])
    assert len(rows) == 7 and len(columns) == 10 and rank(rows) == 7

    s4 = load("s4_rowspace_obstruction.json")
    a, n, target = s4["rows"], s4["dual_witness"], s4["target"]
    assert len(a) == 134 and len(n) == len(target) == 23
    assert all(sum(x * y for x, y in zip(row, n)) == 0 for row in a)
    assert sum(x * y for x, y in zip(target, n)) == 24
    assert rank(a) == 19 and rank(a + [target]) == 20

    intervals = load("gaussian_intervals.json")
    component_count = 0
    for triple in intervals["triples"]:
        for key in ("real_part", "imaginary_part"):
            lo, hi = read_interval(triple[key])
            assert hi - lo < Fraction(1, 10**90)
            component_count += 1
        lo, hi = read_interval(triple["printed_identity_residual"])
        assert lo <= 0 <= hi
    assert component_count == 6
    report = {
        "status": "PASS",
        "dependencies": "Python standard library only",
        "catalogue_entries_replayed": len(catalogue),
        "triple_matrix_rank": 7,
        "s4_matrix_rank": 19,
        "s4_augmented_rank": 20,
        "s4_dual_pairing": 24,
        "rational_component_width_checks": component_count,
        "qualification": "Finite algebra and stored enclosure widths only; analytic soundness and tail estimates are separate proof obligations addressed in the article.",
    }
    (ROOT / "certificates" / "certificate_replay_report.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
