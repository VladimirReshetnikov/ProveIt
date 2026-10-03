#!/usr/bin/env python3
"""Exact validation and exports for binary and one-coordinate feature compilers."""
from __future__ import annotations
import json
import random
from itertools import product
from pathlib import Path
from polynomial_histories import (
    CA, ONE, add, compile_system, compile_feature_system, elementary_ca,
    example_ca, encode_poly, is_first_single_acceptance, multiply,
    witness_for_horizon,
)
from export_quadratic import expand_quadratic, evaluate_expanded


def compare_rule(ca, word, horizons):
    symbol = compile_system(ca, word)
    binary = compile_feature_system(ca, word)
    weighted = compile_feature_system(ca, word, features=[(a,) for a in range(ca.size)])
    assert binary.variables == weighted.variables == symbol.variables
    assert len(binary.equations) == 6+3*(ca.size-1).bit_length()
    for equation in binary.equations:
        assert all(len(p) <= 2 and all(abs(c) <= 1 and i+j <= 3 for (i,j),c in p.items())
                   for p in equation.coefficients.values())
    for h in horizons:
        witness, history = witness_for_horizon(symbol, h)
        expected = is_first_single_acceptance(ca, history)
        assert (not symbol.residuals(witness)) == expected
        assert (not binary.residuals(witness)) == expected
        assert (not weighted.residuals(witness)) == expected
    return len(horizons)


def main():
    output = Path(__file__).resolve().parents[1] / "results"
    output.mkdir(parents=True, exist_ok=True)
    binary_cases = multistate_cases = 0
    for rule in range(0, 256, 2):
        ca = elementary_ca(rule)
        for m in range(1, 4):
            for word in product(range(2), repeat=m):
                binary_cases += compare_rule(ca, word, range(4))
    rng = random.Random(20261003)
    for s in (3, 4, 5, 8):
        for _ in range(12):
            table = {t: rng.randrange(s) for t in product(range(s), repeat=3)}
            table[(0,0,0)] = 0
            ca = CA(s, table, frozenset({s-1}))
            word = tuple(rng.randrange(s-1) for _ in range(rng.randrange(1,5)))
            multistate_cases += compare_rule(ca, word, range(6))
    ca, word = example_ca(), (1,0,0,0,2)
    symbol = compile_system(ca, word)
    witness, _ = witness_for_horizon(symbol, 4)
    exported = {}
    for name, system in (
        ("binary", compile_feature_system(ca, word)),
        ("weighted", compile_feature_system(ca, word, features=[(a,) for a in range(ca.size)])),
    ):
        assert not system.residuals(witness)
        mutations = 0
        for key, poly in witness.items():
            for exponent in poly:
                for delta in (-1,1):
                    changed = {k: dict(v) for k,v in witness.items()}
                    changed[key][exponent] += delta
                    if not changed[key][exponent]:
                        del changed[key][exponent]
                    assert system.residuals(changed)
                    mutations += 1
            for exponent in ((0,9), (20,0), (20,9)):
                changed = {k: dict(v) for k,v in witness.items()}
                changed[key][exponent] = 1
                assert system.residuals(changed)
                mutations += 1
        quadratic = expand_quadratic(system)
        assert not evaluate_expanded(quadratic, witness)
        changed = {k: dict(v) for k,v in witness.items()}
        changed["D"] = add(changed["D"], ONE)
        residuals = system.residuals(changed)
        assert evaluate_expanded(quadratic, changed) == add(*(multiply(p,p) for p in residuals.values()))
        stats = {"variables":len(system.variables), "equations":len(system.equations),
                 "coefficient_magnitude_bound":max(abs(c) for e in system.equations for p in e.coefficients.values() for c in p.values()),
                 "rejected_mutations":mutations,
                 "quadratic_unknown_monomials":len(quadratic),
                 "quadratic_expanded_terms":sum(len(p) for p in quadratic.values()),
                 "exact_expanded_evaluation_checks":2}
        with (output/f"example_{name}_system.json").open("w") as stream:
            json.dump(system.serializable(), stream, indent=2)
        with (output/f"example_{name}_quadratic.json").open("w") as stream:
            json.dump({"statistics":stats, "terms":[{"unknowns":list(k),"coefficient":encode_poly(p)}
                      for k,p in sorted(quadratic.items())]}, stream, indent=2)
        exported[name] = stats
    # Matrix invariance includes different length and different symbol content.
    for features in (None, [(a,) for a in range(ca.size)]):
        ref = compile_feature_system(ca, word, features=features)
        other = compile_feature_system(ca, (3,2,1,0,0,0,0), features=features)
        assert [r.coefficients for r in ref.equations] == [r.coefficients for r in other.equations]
    for bad in (((0,),)*4, ((1,), (2,), (3,), (4,)), ((0,), (1,), (2,), (-3,))):
        try:
            compile_feature_system(ca, word, features=bad)
        except ValueError:
            pass
        else:
            raise AssertionError("Invalid feature map accepted.")
    # The degenerate one-symbol alphabet uses zero features, hence six rows.
    unary = CA(1, {(0,0,0):0}, frozenset())
    assert len(compile_feature_system(unary, (0,)).equations) == 6
    report={"status":"all exact assertions passed", "binary_rule_input_horizon_cases":binary_cases,
            "multistate_cases":multistate_cases, "feature_system_checks_per_case":2,
            "multistate_seed":20261003,"example_forms":exported,
            "invalid_feature_maps_rejected":3,"matrix_invariance_checks":2}
    with (output/'feature_results.json').open('w') as stream:
        json.dump(report,stream,indent=2)
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
