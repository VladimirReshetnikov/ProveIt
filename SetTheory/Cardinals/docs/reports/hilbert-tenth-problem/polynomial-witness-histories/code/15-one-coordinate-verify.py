"""Reproducible exact finite checks. These are tests, not a proof assistant.

Run from any directory. --part selects one suite; no argument runs all suites.
Individual suite JSON files and verification.json are deterministic receipts.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from itertools import product
from pathlib import Path
import json
import random

from compiler import (Rule, add, scale, shift, mul, mono, rep, compile_system,
                      candidate, example_rule, evaluate, tile_name)
from bounded_linear import solve

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results"


def dense_truth(rule: Rule, word: tuple[int, ...], horizon: int) -> bool:
    """Independent fixed-window reference; no certificate clocks or packing."""
    pad = horizon + 2
    state = [0] * pad + list(word) + [0] * pad
    counts = []
    for t in range(horizon + 1):
        counts.append(sum(a in rule.accepting for a in state))
        if t != horizon:
            state = [rule.table[((state[i - 1] if i else 0) * rule.s + state[i]) * rule.s
                                + (state[i + 1] if i + 1 < len(state) else 0)]
                     for i in range(len(state))]
    return counts[-1] == 1 and not any(counts[:-1])


def binary_suite() -> dict:
    cases = accepted = 0
    for bits in product(range(2), repeat=7):
        rule = Rule(2, (0,) + bits, frozenset({1}))
        for m in range(1, 4):
            for word in product(range(2), repeat=m):
                system = compile_system(rule, word)
                for h in range(4):
                    got = system.accepts(candidate(system, h))
                    assert got == dense_truth(rule, word, h), (bits, word, h)
                    cases += 1
                    accepted += got
    return {"cases": cases, "admitted": accepted,
            "scope": "all 128 quiescent binary rules, word lengths 1..3, horizons 0..3"}


def multistate_suite() -> dict:
    rng = random.Random(20261002)
    cases = admitted = feature_checks = 0
    for s in (3, 4, 5):
        features = tuple(tuple((a >> k) & 1 for k in range((s - 1).bit_length()))
                         for a in range(s))
        for _ in range(8):
            rule = Rule(s, (0,) + tuple(rng.randrange(s) for _ in range(s ** 3 - 1)),
                        frozenset({s - 1}))
            for _ in range(4):
                word = tuple(rng.randrange(s) for _ in range(rng.randrange(1, 5)))
                weighted = compile_system(rule, word)
                binary = compile_system(rule, word, features=features)
                for h in range(6):
                    witness = candidate(weighted, h)
                    expected = dense_truth(rule, word, h)
                    assert weighted.accepts(witness) == expected
                    assert binary.accepts(witness) == expected
                    cases += 1
                    admitted += expected
                    feature_checks += 1
    return {"seed": 20261002, "cases": cases, "admitted": admitted,
            "additional_binary_feature_checks": feature_checks}


def ray_geometry_suite() -> dict:
    ray_cases = admitted = 0
    for digits in product(range(3), repeat=8):
        E = {i: c for i, c in enumerate(digits) if c}
        S = add(mono(1), shift(E, 1), scale(E, -1))
        ray_cases += 1
        if all(c >= 0 for c in S.values()):
            assert len(S) == 1 and next(iter(S.values())) == 1
            W = next(iter(S))
            assert W >= 1 and E == rep(W - 1, 1)
            admitted += 1
    clocks = synchronized = calibrated = 0
    for m, W, h, k in product(range(1, 4), range(1, 10), range(4), range(4)):
        Q = {m + 1 + (W + 2) * t: 1 for t in range(h)}
        D = mono(m + 1 + (W + 2) * h)
        B = mono(W * k)
        V = {W * t: 1 for t in range(k)}
        H = {}
        for t in range(h):
            H = add(H, rep(m + 2 * t + 2, W * t))
        shape = add(shift(H, 1), V, scale(H, -1), scale(shift(Q, 1), -1))
        assert (not shape) == (h == k)
        calibration = add(shift(B, W), scale(shift(D, 1), -1))
        if h == k:
            synchronized += 1
            assert (not calibration) == (W == m + 2 * h + 2)
            calibrated += not calibration
        clocks += 1
    return {"ray_candidates": ray_cases, "ray_admitted": admitted,
            "clock_parameter_tuples": clocks, "synchronized": synchronized,
            "calibrated": calibrated}


def independent_tiles_suite() -> dict:
    # Each of three source sites independently chooses one of 8 triples.
    # We do NOT build the source row from a simulated configuration.
    cases = structural = 0
    all_triples = tuple(product(range(2), repeat=3))
    tables = [(0,) + bits for bits in ((0,)*7, (1,)*7, (0,1,0,1,0,1,0), (1,0,1,0,1,0,1))]
    for table in tables:
        for symbol in range(2):
            system = compile_system(Rule(2, table, frozenset({1})), (symbol,))
            base = candidate(system, 1)
            for chosen in product(all_triples, repeat=3):
                witness = {name: dict(p) for name, p in base.items()}
                for name in system.names:
                    if name.startswith("z_") or name.startswith("t_"):
                        witness[name] = {}
                # W=5, top guards occupy exponents 5 and 9.
                witness["t_0"] = {5: 1, 9: 1}
                for j, triple in enumerate(chosen):
                    name = tile_name(triple)
                    witness[name][j] = 1
                    topname = f"t_{system.rule.output(*triple)}"
                    witness[topname][6 + j] = 1
                residuals = system.evaluate(witness)
                got = not any(p for name, p in residuals.items()
                              if name not in {"no_earlier_acceptance", "singleton_terminal"})
                actual = ((0, 0, symbol), (0, symbol, 0), (symbol, 0, 0))
                assert got == (chosen == actual)
                structural += got
                cases += 1
    return {"independent_assignments": cases, "structurally_admitted": structural,
            "scope": "four rules, two one-letter inputs, all 8^3 source-tile assignments"}


def mutation_suite() -> dict:
    system = compile_system(example_rule(), (1, 0, 0, 0, 2))
    witness = candidate(system, 4)
    assert system.accepts(witness)
    changes = 0
    for name, p in witness.items():
        for e in p:
            for value in (0, 2):
                altered = deepcopy(witness)
                altered[name][e] = value
                assert not system.accepts(altered), (name, e, value)
                changes += 1
    insertions = 0
    for name in system.names:
        altered = deepcopy(witness)
        altered[name][100] = 1
        assert not system.accepts(altered), name
        insertions += 1
    horizons = 0
    for h in range(8):
        assert system.accepts(candidate(system, h)) == (h == 4)
        horizons += 1
    strides = 0
    for W in range(15, 23):
        result = system.evaluate(candidate(system, 4, width=W))
        assert not any(p for name, p in result.items() if name != "calibration")
        assert (not result["calibration"]) == (W == 15)
        strides += 1
    # Literal false certificate admitted when the positive-stride row is deleted.
    zero = compile_system(Rule(2, (0,) * 8, frozenset({1})), (0,))
    ghost = {name: {} for name in zero.names}
    ghost.update({"q": {2: 1}, "v": {0: 1}, "z_0_0_0": rep(3)})
    result = zero.evaluate(ghost)
    assert result["positive_stride"] == {1: -1}
    assert not any(p for name, p in result.items() if name != "positive_stride")
    return {"coefficient_deletions_and_doublings": changes,
            "off_region_insertions": insertions, "horizons_checked": horizons,
            "strides_checked": strides, "zero_stride_ghost_reproduced": True}


def bounded_linear_suite() -> dict:
    cases = admitted = 0
    bound_degree = 6  # m + (B+1)^(nd) = 2 + 2^2.
    binary_polys = [{t: a for t, a in enumerate(digits) if a}
                    for digits in product(range(2), repeat=bound_degree + 1)]
    for a in product((-1, 0, 1), repeat=3):
        A = [[[c]] for c in a]
        ap = {t: c for t, c in enumerate(a) if c}
        products = {tuple(sorted(mul(ap, u).items())) for u in binary_polys}
        for b in product((-1, 0, 1), repeat=3):
            rhs = {t: c for t, c in enumerate(b) if c}
            result = solve(A, [[c] for c in b], 1)
            brute = tuple(sorted(rhs.items())) in products
            assert (result is not None) == brute, (a, b)
            if result is not None:
                assert mul(ap, result[0]) == rhs
                assert all(c in (0, 1) for c in result[0].values())
                assert max(result[0], default=-1) <= bound_degree
                admitted += 1
            cases += 1
    # d=0, B=0, two variables, and negative matrix coefficients.
    extra = [([[[1]]], [[2]], 2, True),
             ([[[1]]], [[1]], 0, False),
             ([[[1, -1]]], [[0]], 1, True),
             ([[[1, 1]], [[-1, 0]]], [[1], [0]], 1, True)]
    for A, b, B, yes in extra:
        assert (solve(A, b, B) is not None) == yes
    return {"scalar_systems": cases, "admitted": admitted,
            "brute_polynomials_per_system": len(binary_polys),
            "brute_degree_limit": bound_degree, "extra_edge_cases": len(extra)}


def interface_suite() -> dict:
    rule = example_rule()
    system = compile_system(rule, (1, 0, 0, 0, 2))
    witness = candidate(system, 4)
    rejected = 0
    tests = []
    for field, key, value in (("b", True, 1), ("b", 0, True), ("b", -1, 1),
                               ("b", 0, -1), ("b", 0, 0.5)):
        changed = deepcopy(witness)
        changed[field][key] = value
        tests.append(lambda changed=changed: system.accepts(changed))
    missing = deepcopy(witness)
    missing.pop("b")
    tests.append(lambda: system.accepts(missing))
    tests += [lambda: compile_system(rule, ()), lambda: compile_system(rule, (True,)),
              lambda: candidate(system, True),
              lambda: Rule(2, (1,) * 8, frozenset({1})),
              lambda: Rule(2, (0,) * 8, frozenset({0})),
              lambda: compile_system(rule, (1,), features=((0,), (1,), (1,), (2,)))]
    for fn in tests:
        try:
            fn()
        except ValueError:
            rejected += 1
        else:
            raise AssertionError("invalid input was not rejected")
    # Source table and feature source mutation must not mutate the compiler.
    table = list(rule.table)
    owned = Rule(4, table, {3})
    table[1] = (table[1] + 1) % 4
    assert owned.table == rule.table
    assert len(system.names) == 75 and len(system.residuals) == 11
    assert all(len(names) <= 2 for row in system.residuals.values() for e, names in row)
    assert all("stride" in names for row in system.residuals.values()
               for e, names in row if len(names) == 2)
    for row in system.residuals.values():
        for (e, names), c in row.items():
            if names:
                assert e <= 2 and abs(c) <= 3
    # Matrix/polynomial template nonconstant terms independent of word and length.
    other = compile_system(rule, (2, 1))
    for name in system.residuals:
        left = {key: c for key, c in system.residuals[name].items() if key[1]}
        right = {key: c for key, c in other.residuals[name].items() if key[1]}
        assert left == right
    return {"invalid_input_rejections": rejected, "immutable_table_check": True,
            "template_invariance_check": True, "shared_stride_and_degree_checks": True}


SUITES = {"binary": binary_suite, "multistate": multistate_suite,
          "ray_geometry": ray_geometry_suite, "independent_tiles": independent_tiles_suite,
          "mutations": mutation_suite, "bounded_linear": bounded_linear_suite,
          "interfaces": interface_suite}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--part", choices=tuple(SUITES))
    args = parser.parse_args()
    RESULTS.mkdir(exist_ok=True)
    for name, fn in SUITES.items():
        if args.part and name != args.part:
            continue
        result = {"status": "passed", **fn()}
        (RESULTS / f"test_{name}.json").write_text(json.dumps(result, indent=2) + "\n")
        print(name, json.dumps(result), flush=True)
    receipts = {name: json.loads((RESULTS / f"test_{name}.json").read_text())
                for name in SUITES if (RESULTS / f"test_{name}.json").exists()}
    (RESULTS / "verification.json").write_text(json.dumps({
        "all_suites_present": len(receipts) == len(SUITES), "suites": receipts,
        "qualification": "Finite exact tests, not a formal proof or independent referee audit."
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
