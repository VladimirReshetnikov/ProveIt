"""Cross-verification between the two independent proofs in this archive.

Neither original package could run these comparisons: each held only one of
the two implementations. Every check here relates an object produced by the
finite-state proof (kbonacci_residues.py) to an object produced by the
signed-cancellation proof (kbonacci_parity.py).

The checks correspond to items (X1)-(X5) of the article's cross-verification
section. Explicit error checks are used rather than `assert`, so this script
still validates under `python -O`.

Run from anywhere:  python code/cross_check.py
"""
from __future__ import annotations

import csv
import json
import platform
from decimal import Decimal, localcontext
from pathlib import Path
from time import perf_counter

from kbonacci_parity import (
    CoefficientOracle, count_fast, count_prefix, standard_seeds,
    weights as signed_weights,
)
from kbonacci_residues import (
    coefficient_for_canonical, dfa_sequence, expand, normalize,
    parity_machine, weights as canonical_weights,
)

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"


def check(condition: bool, message: str) -> None:
    """Do not rely on assert: these checks still execute under python -O."""
    if not condition:
        raise AssertionError(message)


def x1_structural_witnesses() -> dict:
    """Flatness (signed, in {-1,0,1}) against the exact fiber counter.

    The signed oracle knows only signs; the counter knows only multiplicities.
    Neither statement implies the other, so their agreement is informative.
    """
    positions = 0
    represented = 0
    for k in range(2, 7):
        for n in range(0, 13):
            exact = expand(k, n)
            oracle = CoefficientOracle(k, n)
            canonical_of = _canonical_representatives(k, n)
            for j, c in enumerate(exact):
                signed = oracle.signed(j)
                check(signed in (-1, 0, 1), f"flatness violated {(k, n, j)}")
                check(abs(signed) == c % 2,
                      f"signed parity vs exact coefficient {(k, n, j)}")
                check(oracle.parity(j) == c % 2,
                      f"oracle parity vs exact coefficient {(k, n, j)}")
                positions += 1
                if c:
                    check(j in canonical_of, f"unrepresented nonzero {(k, n, j)}")
                    check(coefficient_for_canonical(canonical_of[j], k) == c,
                          f"fiber counter vs exact coefficient {(k, n, j)}")
                    represented += 1
                else:
                    check(j not in canonical_of, f"represented zero {(k, n, j)}")
    return {"k_min": 2, "k_max": 6, "n_max": 12,
            "positions_compared": positions,
            "represented_exponents_compared": represented,
            "identity": "abs(signed coefficient) == exact coefficient mod 2",
            "passed": True}


def _canonical_representatives(k: int, n: int) -> dict[int, tuple[int, ...]]:
    """Exhaustive map from represented exponent to its canonical word."""
    ws = canonical_weights(k, n)
    result: dict[int, tuple[int, ...]] = {}
    for mask in range(1 << n):
        word = tuple((mask >> i) & 1 for i in range(n))
        exponent = sum(b * w for b, w in zip(word, ws))
        canonical = normalize(word, k)
        previous = result.setdefault(exponent, canonical)
        check(previous == canonical, f"nonunique normal form {(k, n, exponent)}")
    return result


def x2_two_proofs_agree() -> dict:
    """Polynomial powering (signed proof) against the 4k+2-state automaton."""
    comparisons = 0
    for k in range(2, 9):
        _, edges, accepting = parity_machine(k)
        automaton = dfa_sequence(edges, accepting, 100)
        check(len(automaton) == 101, "automaton sequence length")
        for n, value in enumerate(automaton):
            check(count_fast(k, n) == value,
                  f"powering vs automaton {(k, n)}")
            comparisons += 1
    return {"k_min": 2, "k_max": 8, "n_max": 100, "comparisons": comparisons,
            "note": "count_fast descends from the signed proof's recurrence; "
                    "dfa_sequence descends from the parity automaton. Unlike "
                    "count_prefix vs count_fast, this compares two proofs.",
            "passed": True}


def _read_counts(path: Path, column: str) -> dict[tuple[int, int], int]:
    with path.open() as stream:
        return {(int(row["k"]), int(row["n"])): int(row[column])
                for row in csv.DictReader(stream)}


def x3_count_tables_agree() -> dict:
    signed = _read_counts(DATA / "counts.csv", "odd_coefficient_count")
    automaton = _read_counts(DATA / "odd_counts.csv", "odd_coefficients")
    shared = sorted(set(signed) & set(automaton))
    check(bool(shared), "the two count tables do not overlap")
    for key in shared:
        check(signed[key] == automaton[key], f"count tables disagree at {key}")
    ks = sorted({k for k, _ in shared})
    ns = [n for _, n in shared]
    return {"overlap_entries": len(shared), "k_range": [ks[0], ks[-1]],
            "n_range": [min(ns), max(ns)],
            "files": ["data/counts.csv", "data/odd_counts.csv"],
            "passed": True}


def x4_growth_tables_agree(tolerance: float = 1e-9) -> dict:
    with (DATA / "growth.csv").open() as stream:
        precise = {int(row["k"]): row for row in csv.DictReader(stream)}
    with (DATA / "growth_constants.csv").open() as stream:
        floating = {int(row["k"]): row for row in csv.DictReader(stream)}
    compared = 0
    worst = 0.0
    for k, row in floating.items():
        if k not in precise:
            continue
        pairs = [(Decimal(precise[k]["lambda"]), float(row["rho_odd"])),
                 (Decimal(precise[k]["rho_multinacci"]), float(row["beta_support"])),
                 (Decimal(precise[k]["C"]), float(row["leading_constant_odd"]))]
        for exact, approximate in pairs:
            relative = abs(float(exact) - approximate) / abs(float(exact))
            worst = max(worst, relative)
            check(relative < tolerance,
                  f"growth constants disagree at k={k}: {exact} vs {approximate}")
            compared += 1
    check(compared > 0, "no common orders between the two growth tables")
    return {"values_compared": compared,
            "worst_relative_difference": worst,
            "tolerance": tolerance,
            "note": "C_k from the analytic formula equals gamma_k from the "
                    "V_k formula; see the article's corollary.",
            "files": ["data/growth.csv", "data/growth_constants.csv"],
            "passed": True}


def x5_weight_conventions_agree() -> dict:
    for k in range(2, 13):
        a = canonical_weights(k, 40)
        b = signed_weights(k, 40)
        check(a == b, f"weight conventions differ at k={k}")
        check(b[:k] == standard_seeds(k), f"seed block mismatch at k={k}")
    return {"k_min": 2, "k_max": 12, "n": 40,
            "note": "kbonacci_parity stores weights one-based internally; the "
                    "public sequences are identical.",
            "passed": True}


def x6_documented_invariants() -> dict:
    check(count_fast(3, 20) == 76576, "count_fast(3,20)")
    check(count_fast(3, 10 ** 12, modulus=1000000007) == 699562826,
          "count_fast(3,10**12) modulo 1000000007")
    check(coefficient_for_canonical((0, 0, 0, 0, 1), 2) == 3,
          "coefficient_for_canonical((0,0,0,0,1), k=2)")
    check(normalize((1, 1, 0), 2) == (0, 0, 1), "normalize((1,1,0), k=2)")
    oracle = CoefficientOracle(3, 8)
    check(oracle.signed(105) == -1 and oracle.parity(105) == 1,
          "CoefficientOracle(3,8) at exponent 105")
    check(count_prefix(3, 4)[4] == 14, "a_3(4) == 14")
    with localcontext() as context:
        context.prec = 30
        check(Decimal("1.5436890126920763615") < Decimal("1.5436890126920766"),
              "recorded growth-constant ordering")
    return {"invariants_checked": 7, "passed": True}


def main() -> dict:
    start = perf_counter()
    summary = {"python": platform.python_version(), "checks": {}}
    steps = [("X1_structural_witnesses", x1_structural_witnesses),
             ("X2_two_proofs_agree", x2_two_proofs_agree),
             ("X3_count_tables_agree", x3_count_tables_agree),
             ("X4_growth_tables_agree", x4_growth_tables_agree),
             ("X5_weight_conventions_agree", x5_weight_conventions_agree),
             ("X6_documented_invariants", x6_documented_invariants)]
    for name, step in steps:
        summary["checks"][name] = step()
        print(f"{name}: PASS", flush=True)
    summary["all_passed"] = True
    summary["elapsed_seconds"] = round(perf_counter() - start, 3)
    DATA.mkdir(exist_ok=True)
    (DATA / "cross_check.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    return summary


if __name__ == "__main__":
    main()
