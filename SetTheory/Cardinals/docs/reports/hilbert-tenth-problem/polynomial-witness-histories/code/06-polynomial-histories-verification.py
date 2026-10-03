#!/usr/bin/env python3
"""Reproducible exact tests; no external packages are required.

The tests are not a proof assistant or a substitute for the article's proof.
They exercise the COMPLETE affine-linear equations, including boundary,
clock, and acceptance rows, with coefficientwise arbitrary-precision integers.
"""
from __future__ import annotations

import argparse
import json
import random
import time
from itertools import product
from pathlib import Path

from polynomial_histories import (
    CA, ONE, add, compile_system, elementary_ca, encode_poly, example_ca,
    is_first_single_acceptance, is_natural, monomial, scale, shift,
    tile_name, witness_for_horizon, witness_statistics,
)


def check_candidate(system, h):
    witness, history = witness_for_horizon(system, h)
    residuals = system.residuals(witness)
    semantic = is_first_single_acceptance(system.ca, history)
    assert (not residuals) == semantic
    assert set(residuals) <= {"no_early_acceptance", "one_final_acceptance"}
    stats = witness_statistics(witness)
    assert stats["boolean_coefficients"]
    m = len(system.word)
    assert stats["max_X_degree"] == m + 2 * h + 1
    assert stats["max_Y_degree"] == h
    assert stats["max_total_degree"] == m + 3 * h + 1
    if semantic:
        top = (0,) + history[-1] + (0,)
        j = next(i for i, a in enumerate(top) if a in system.ca.accepting)
        assert stats["total_nonzero_coefficients"] == h*h + m*h + 5*h + m + 4 + j
    return semantic


def clock_exhaustion():
    grid = list(product(range(3), repeat=2))
    cases = accepted = 0
    for dx, dy in [(0, 1), (1, 1), (2, 1)]:
        for coefficients in product(range(3), repeat=len(grid)):
            q = {e: c for e, c in zip(grid, coefficients) if c}
            d = add(ONE, shift(q, dx, dy), scale(q, -1))
            cases += 1
            if not is_natural(d):
                continue
            accepted += 1
            assert len(d) == 1 and sum(d.values()) == 1
            h = sum(q.values())
            assert d == monomial(dx*h, dy*h)
            assert q == {(dx*t, dy*t): 1 for t in range(h)}
    return {"candidate_flows": cases, "admitted_ray_clocks": accepted}


def binary_exhaustion():
    cases = accepted = 0
    for rule in range(0, 256, 2):
        ca = elementary_ca(rule)
        for m in range(1, 5):
            for word in product(range(2), repeat=m):
                system = compile_system(ca, word)
                for h in range(5):
                    accepted += check_candidate(system, h)
                    cases += 1
    return {"quiescent_rules": 128, "input_words_per_rule": 30,
            "horizons_per_word": 5, "cases": cases, "accepted": accepted}


def random_multistate_tests():
    rng = random.Random(20261002)
    cases = accepted = 0
    for s in (3, 4, 5):
        for _ in range(40):
            table = {t: rng.randrange(s) for t in product(range(s), repeat=3)}
            table[(0, 0, 0)] = 0
            ca = CA(s, table, frozenset({s-1}))
            m = rng.randrange(1, 7)
            # Usually avoid accepting input states to test genuine later events.
            word = tuple(rng.randrange(s-1) for _ in range(m))
            system = compile_system(ca, word)
            for h in range(7):
                accepted += check_candidate(system, h)
                cases += 1
    return {"seed": 20261002, "rules": 120, "cases": cases, "accepted": accepted}


def independent_tile_exhaustion():
    rules = [0, 2, 18, 22, 30, 54, 60, 90, 102, 110, 126, 150, 178, 184, 204, 254]
    triples = list(product(range(2), repeat=3))
    cases = admitted = 0
    for rule in rules:
        ca = elementary_ca(rule)
        for bit in (0, 1):
            system = compile_system(ca, (bit,))
            pair_system = compile_system(ca, (bit,), horizontal="pair")
            base, _ = witness_for_horizon(system, 1)
            for selected in product(triples, repeat=3):
                witness = {name: dict(p) for name, p in base.items()}
                for t in triples:
                    witness[tile_name(t)] = {}
                for a in range(2):
                    witness[f"T_{a}"] = {}
                for j, t in enumerate(selected):
                    witness[tile_name(t)][(j, 0)] = 1
                    witness[f"T_{ca.table[t]}"][(j+1, 1)] = 1
                witness["T_0"][(0, 1)] = 1
                witness["T_0"][(4, 1)] = 1
                residuals = system.residuals(witness)
                structural = {name: p for name, p in residuals.items()
                              if name not in ("no_early_acceptance", "one_final_acceptance")}
                pair_residuals = pair_system.residuals(witness)
                pair_structural = {name: p for name, p in pair_residuals.items()
                                   if name not in ("no_early_acceptance", "one_final_acceptance")}
                assert bool(structural) == bool(pair_structural)
                cases += 1
                if not structural:
                    admitted += 1
                    assert selected == ((0, 0, bit), (0, bit, 0), (bit, 0, 0))
    assert admitted == 2 * len(rules)
    return {"rules": len(rules), "independent_tile_assignments": cases,
            "admitted_structural_histories": admitted, "pair_marginal_equivalences_checked": cases}


def matrix_and_domain_tests():
    ca = example_ca()
    reference = compile_system(ca, (1, 2))
    matrix = [e.coefficients for e in reference.equations]
    for word in ((0,), (3,), (1, 0, 0, 2), (2,)*11):
        assert [e.coefficients for e in compile_system(ca, word).equations] == matrix
    for row in reference.equations:
        for poly in row.coefficients.values():
            assert len(poly) <= 2
            assert all(c in (-1, 1) and i+j <= 3 for (i, j), c in poly.items())
    failures = 0
    for attempt in (
        lambda: compile_system(ca, ()),
        lambda: compile_system(ca, (9,)),
        lambda: witness_for_horizon(reference, -1),
        lambda: elementary_ca(1),
        lambda: reference.residuals({}),
    ):
        try:
            attempt()
        except ValueError:
            failures += 1
        else:
            raise AssertionError("Invalid input was accepted.")
    source = dict(ca.table)
    copy = CA(ca.size, source, ca.accepting)
    source[(0, 0, 0)] = 3
    assert copy.table[(0, 0, 0)] == 0
    return {"matrix_invariance_cases": 4, "invalid_inputs_rejected": failures,
            "coefficient_magnitude_bound": 1, "coefficient_total_degree_bound": 3,
            "maximum_terms_per_matrix_entry": 2, "mutable_source_is_copied": True}


def example_and_mutations(output: Path):
    system = compile_system(example_ca(), (1, 0, 0, 0, 2))
    witness, history = witness_for_horizon(system, 4)
    assert not system.residuals(witness)
    stats = witness_statistics(witness)
    rejected = 0
    for name, poly in witness.items():
        for e in poly:
            for delta in (-1, 1):
                changed = {k: dict(v) for k, v in witness.items()}
                changed[name][e] += delta
                if not changed[name][e]:
                    del changed[name][e]
                assert system.residuals(changed)
                rejected += 1
        for e in ((0, 9), (20, 0), (20, 9)):
            changed = {k: dict(v) for k, v in witness.items()}
            changed[name][e] = 1
            assert system.residuals(changed)
            rejected += 1
    for h in (0, 1, 2, 3, 5, 6):
        other, _ = witness_for_horizon(system, h)
        assert system.residuals(other)
        rejected += 1
    with (output / "example_system.json").open("w") as stream:
        json.dump(system.serializable(), stream, indent=2)
    with (output / "example_certificate.json").open("w") as stream:
        json.dump({"horizon": 4, "history": [list(row) for row in history],
                   "variables": {name: encode_poly(p) for name, p in witness.items()},
                   "statistics": stats, "nonzero_residuals": {}}, stream, indent=2)
    return {"input": list(system.word), "horizon": 4, "variables": len(system.variables),
            "equations": len(system.equations), **stats, "mutations_or_wrong_horizons_rejected": rejected}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "results")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()
    report = {"clock_exhaustion": clock_exhaustion(),
              "binary_exhaustion": binary_exhaustion(),
              "multistate_tests": random_multistate_tests(),
              "independent_tile_exhaustion": independent_tile_exhaustion(),
              "matrix_and_domain_tests": matrix_and_domain_tests(),
              "worked_example": example_and_mutations(args.output)}
    report["elapsed_seconds"] = round(time.perf_counter()-start, 3)
    report["status"] = "all exact assertions passed"
    report["proof_status"] = "computational validation, not a proof-assistant formalization"
    with (args.output / "verification_results.json").open("w") as stream:
        json.dump(report, stream, indent=2)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
