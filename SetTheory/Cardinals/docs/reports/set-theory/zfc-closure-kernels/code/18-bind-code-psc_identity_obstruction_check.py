#!/usr/bin/env python3
"""Finite exact regressions for the PSC identity-quantifier obstruction.

The accompanying Lean file proves the arbitrary-formula/derivation statement.
This script independently evaluates the *actual pinned* Python PSC template,
checks both of its numerical decoder conventions, and retains a negative C/G
control to prevent applying the PSC result to another candidate.

No machine simulation or Con(ZFC) calibration is claimed.
"""
from __future__ import annotations

import argparse
from functools import cache
from hashlib import sha256
from itertools import product
from math import isqrt
from pathlib import Path
import json
import sys


def unpair(n: int) -> tuple[int, int]:
    d = (isqrt(8 * n + 1) - 1) // 2
    b = n - d * (d + 1) // 2
    return d - b, b


def relation(i: int, j: int) -> bool:
    return i >= 2 and j == 0


@cache
def code_value(base: int, n: int) -> bool:
    if n == 0:
        return True
    tag = n % base
    if base == 4 and tag == 1:
        return False
    i, j = unpair(n // base)
    if tag == 0:
        return not code_value(base, i) or code_value(base, j)
    if tag == (1 if base == 3 else 2):
        return relation(i, j)
    return code_value(base, j)


def actual_value(p, formula_values: dict[str, bool], labels: dict[str, int]) -> bool:
    """Interpret the generator's expanded Imp/Rel/All AST literally."""
    if p == 0:
        return True
    if p == 1:
        return False  # R(0,0) and primitive Bottom both have this value.
    if isinstance(p, str):
        return formula_values[p]
    tag, a, b = p
    if tag == "imp":
        return not actual_value(a, formula_values, labels) or actual_value(b, formula_values, labels)
    if tag == "all":
        return actual_value(b, formula_values, labels)
    if tag == "rel":
        return relation(labels.get(a, a), labels.get(b, b))
    raise AssertionError(("unexpected constructor", p))


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O; the audit requires assertions.")
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--limit", type=int, default=100000)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    source = args.repo / "Computability/BusyBeaver/Research/ZFC"
    sys.path.insert(0, str(source))
    import psc_backend_experiment as psc_source
    import theory_backend_experiment as theory_source

    template = psc_source.psc_template("k")
    template_cases = 0
    for k in list(range(2, 102)) + [2**64 + 17, 10**100]:
        for matrix in (False, True):
            assert actual_value(template, {"c": matrix}, {"k": k})
            template_cases += 1

    decoder_cases = {}
    for base in (3, 4):
        false_matrices = true_matrices = 0
        for c in range(args.limit):
            value = code_value(base, c)
            assert actual_value(template, {"c": value}, {"k": c + 2})
            true_matrices += int(value)
            false_matrices += int(not value)
        assert code_value(base, 1) is False
        assert code_value(base, 0) is True
        decoder_cases[str(base)] = {
            "codes": args.limit,
            "false_matrix_evaluations": false_matrices,
            "true_matrix_evaluations": true_matrices,
            "all_psc_rows_valid": True,
        }

    spec, _ = theory_source.published_spec()
    rows = spec["ax_rows"]("a", "h", "b", "c", "u")
    dual = theory_source.Imp("b", theory_source.All("a", theory_source.Ex("a", "b")))
    same = theory_source.Imp(theory_source.All("a", "b"), "b")
    four = theory_source.Imp(theory_source.All("a", "b"), theory_source.All("a", theory_source.All("a", "b")))
    logical_cases = 0
    for values in product((False, True), repeat=5):
        env = dict(zip(("a", "h", "b", "c", "u"), values))
        for labels_tuple in product(range(4), repeat=3):
            labels = dict(zip(("a", "b", "c"), labels_tuple))
            for row in (rows[1], rows[3], rows[5], rows[7], dual, same, four):
                assert actual_value(row, env, labels)
                logical_cases += 1
            # GEN soundness: identity quantifiers leave theorem truth fixed.
            assert actual_value(rows[0], env, labels) == env["h"]
            vacuity = theory_source.Imp(theory_source.Rel("a", "b"), theory_source.All("c", theory_source.Rel("a", "b")))
            assert actual_value(vacuity, env, labels)

    proper_ui = theory_source.Imp(theory_source.All(2, theory_source.Rel(2, 0)), theory_source.Rel(0, 0))
    assert not actual_value(proper_ui, {}, {})
    for i in range(100):
        assert not relation(i, i)

    # Scope guard: this valuation does not validate the C/G candidate's bundle.
    cp = spec["bundle_C"]("a", "b", "c")
    gic = spec["bundle_G"]("a", "b", "c")
    vacuity = theory_source.Imp(theory_source.Rel("a", "b"), theory_source.All("c", theory_source.Rel("a", "b")))
    bundle = theory_source.And(vacuity, theory_source.And(cp, gic))
    cg_labels = {"a": 0, "b": 1, "c": 2}
    cg_formula = {"c": code_value(3, 2)}
    assert cg_labels["c"] not in (cg_labels["a"], cg_labels["b"])
    assert not actual_value(cp, cg_formula, cg_labels)
    assert not actual_value(bundle, cg_formula, cg_labels)

    report = {
        "repository_commit": "96836f9eea3540e96322c3d28c7127a582aae223",
        "source_sha256": {
            name: sha256((source / name).read_bytes()).hexdigest()
            for name in ("psc_backend_experiment.py", "theory_backend_experiment.py")
        },
        "valuation": "All(i,A)=A; Rel(i,j)=(i>=2 and j=0); Bottom=false; Truth=true",
        "actual_psc_template_cases": template_cases,
        "numerical_decoder_cases": decoder_cases,
        "retained_and_additional_logical_row_cases": logical_cases,
        "same_variable_specialization_valid": True,
        "s4_row_valid": True,
        "irreflexivity_samples": 100,
        "proper_ui_sample_false": True,
        "actual_cg_bundle_countercontrol": {"a": 0, "b": 1, "c": 2, "value": False},
        "machine_nonhalting_claimed": False,
        "finite_tests_replace_infinite_schematic_proof": False,
    }
    out = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(out)
    print(out, end="")


if __name__ == "__main__":
    main()
