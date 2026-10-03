"""Export all 11 equations, the complete witness, and the expanded quartic.

No symbolic algebra library is required. Exports use exact sparse monomials.
"""
from __future__ import annotations
from copy import deepcopy
import hashlib
import json
from pathlib import Path

from compiler import (compile_system, example_rule, candidate, expression_json,
                      polynomial_json, evaluate, add, mul)

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results"


def write_json(name: str, value: object) -> None:
    (OUT / name).write_text(json.dumps(value, indent=2) + "\n")


def main() -> None:
    OUT.mkdir(exist_ok=True)
    system = compile_system(example_rule(), (1, 0, 0, 0, 2))
    witness = candidate(system, 4)
    assert system.accepts(witness)
    quartic = system.quartic()
    assert max(len(names) for e, names in quartic) == 4
    tests = [witness]
    for name, e in (("stride", 15), ("d", 74), ("z_0_0_0", 3)):
        changed = deepcopy(witness)
        changed[name][e] = changed[name].get(e, 0) + 1
        tests.append(changed)
    for i, value in enumerate(tests):
        residuals = system.evaluate(value)
        expected = add(*(mul(p, p) for p in residuals.values()))
        actual = evaluate(quartic, value)
        assert actual == expected
        assert (not actual) == (i == 0)
    write_json("example_system.json", {
        "domain": "N[X]", "coordinate_indeterminate": "X",
        "alphabet_size": 4, "rule_table_lexicographic": list(system.rule.table),
        "accepting_symbols": [3], "input_word": list(system.word),
        "variables": list(system.names),
        "semantics": "Each displayed sparse expression is a polynomial identity equal to zero.",
        "residuals": {label: expression_json(expr) for label, expr in system.residuals.items()}
    })
    write_json("example_witness.json", {
        "horizon": 4, "stride": 15, "accepting_position_within_terminal_block": 9,
        "witness": {name: polynomial_json(p) for name, p in witness.items()}
    })
    write_json("example_quartic.json", {
        "domain": "N[X]", "variables": list(system.names),
        "semantics": "Fully expanded sum of squares of the 11 complete residuals.",
        "monomials": expression_json(quartic)
    })
    # Ordinary scalar coefficient expansion at the exact example degree bound.
    # This receipt reports the complete ambient family dimensions, not a hidden
    # constant-arity ordinary Diophantine representation.
    m, h, W, L = 5, 4, 15, 74
    receipt = {
        "status": "passed", "variables": len(system.names),
        "equations": len(system.residuals), "horizon": h, "input_length": m,
        "stride": W, "maximum_witness_degree": L,
        "total_witness_mass": sum(sum(p.values()) for p in witness.values()),
        "nonzero_witness_coefficients": sum(len(p) for p in witness.values()),
        "all_witness_coefficients_boolean": all(c == 1 for p in witness.values() for c in p.values()),
        "residual_term_counts": {label: len(expr) for label, expr in system.residuals.items()},
        "fully_expanded_quartic_terms": len(quartic),
        "unknown_monomials_with_polynomial_coefficients": len({names for e, names in quartic}),
        "quartic_unknown_degree": max(len(names) for e, names in quartic),
        "quartic_coordinate_coefficient_degree": max(e for e, names in quartic),
        "expanded_evaluations": len(tests),
        "ordinary_cutoff_L": L, "ordinary_scalar_variables_at_L": len(system.names) * (L + 1),
        "ordinary_coefficient_rows_before_zero_row_removal": len(system.residuals) * (max(2*L+2, m+1)+1),
    }
    write_json("example_receipt.json", receipt)
    print(json.dumps(receipt, indent=2))
    # Hash just the complete mathematical exports, not the receipt containing hashes.
    write_json("export_hashes.json", {name: hashlib.sha256((OUT / name).read_bytes()).hexdigest()
               for name in ("example_system.json", "example_witness.json", "example_quartic.json")})


if __name__ == "__main__":
    main()
