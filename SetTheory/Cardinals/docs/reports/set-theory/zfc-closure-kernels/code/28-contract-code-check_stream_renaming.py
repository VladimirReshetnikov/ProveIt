#!/usr/bin/env python3
"""Independent finite validation and reproducible certificates for the stream maps.

These tests support the all-input invariant proof in the report. They do
not replace that proof and do not certify a compiled Turing machine.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import random
import time

import stream_renaming as r


def random_formula(rng, size, depth=0):
    if size == 0:
        if rng.randrange(7) == 0:
            return ("bot",)
        def term():
            if depth and rng.randrange(3) == 0:
                return ("b", rng.randrange(depth))
            return ("f", rng.randrange(-8, 9))
        return ("rel", term(), term())
    if rng.randrange(3) == 0:
        return ("all", random_formula(rng, size - 1, depth + 1))
    left = rng.randrange(size)
    return ("imp", random_formula(rng, left, depth),
            random_formula(rng, size - 1 - left, depth))


def run_table(table, bits, mutation=None):
    edges = {(q, str(bit)): (word, target) for q, bit, word, target in table["rows"]}
    state, output, covered = table["initial"], [], set()
    for bit in bits:
        covered.add((state, int(bit)))
        word, target = edges[state, bit]
        if mutation == (state, int(bit)):
            word += "1"
        output.append(word)
        state = target
    if state not in table["accepting"]:
        raise ValueError("incomplete token")
    return "".join(output), covered


def check(output_dir: Path):
    started = time.monotonic()
    output_dir.mkdir(parents=True, exist_ok=True)
    rng = random.Random(20261016)
    tables = {mode: r.table(mode) for mode in r.MODES}
    formulas = [("bot",)]
    # Cover both atom-field positions, every sign boundary, and bound indices.
    for z in range(-20, 21):
        formulas.extend([
            ("rel", ("f", z), ("f", -z)),
            ("all", ("rel", ("b", 0), ("f", z))),
            ("all", ("rel", ("f", z), ("b", 0))),
            ("all", ("all", ("rel", ("b", 1), ("b", 0))))])
    formulas += [random_formula(rng, rng.randrange(16)) for _ in range(4000)]
    witnesses = {mode: {} for mode in r.MODES}
    stream_cases = 0
    for formula in formulas:
        bits = r.encode(formula)
        assert r.decode(bits) == formula
        for mode in r.MODES:
            expected = r.encode(r.rename(formula, lambda z: r.scalar(mode, z)))
            actual, covered = run_table(tables[mode], bits)
            assert actual == expected
            assert r.transduce(mode, bits) == actual
            assert r.decode(actual) == r.rename(formula, lambda z: r.scalar(mode, z))
            for row in covered:
                witnesses[mode].setdefault(row, (bits, expected))
            stream_cases += 1
    scalar_cases = 0
    for mode in r.MODES:
        for z in range(-200, 201):
            a = ("all", ("rel", ("b", 0), ("f", z)))
            assert r.decode(r.transduce(mode, r.encode(a))) == r.rename(a, lambda v: r.scalar(mode, v))
            scalar_cases += 1

    conjugations = 0
    for a in range(-6, 7):
        for b in range(-6, 7):
            word = r.collapse_word(a, b)
            assert word.count("k") == int(a != b)
            for z in range(-8, 9):
                assert r.evaluate_word(word, z) == (b if z == a else z)
                conjugations += 1

    factorizations, worst_word, rank_counts = 0, 0, {}
    domains = [tuple(range(n)) for n in range(6)] + [tuple(range(-2, 3))]
    for domain in domains:
        for values in itertools.product(domain, repeat=len(domain)):
            mapping = dict(zip(domain, values))
            word = r.factor_names(mapping)
            assert all(r.evaluate_word(word, a) == b for a, b in mapping.items())
            loss = len(domain) - len(set(values))
            assert word.count("k") == loss
            rank_counts[loss] = rank_counts.get(loss, 0) + 1
            factorizations += 1
            worst_word = max(worst_word, len(word))
    # Partial maps whose images extend beyond the prescribed domain.
    for _ in range(1000):
        domain = sorted(rng.sample(range(-9, 10), rng.randrange(10)))
        mapping = {a: rng.randrange(-10, 11) for a in domain}
        word = r.factor_names(mapping)
        assert all(r.evaluate_word(word, a) == b for a, b in mapping.items())
        assert word.count("k") == len(domain) - len(set(mapping.values()))
        factorizations += 1
        worst_word = max(worst_word, len(word))

    composed_stream_cases = 0
    for formula in formulas[1:81]:
        mapping = {a: rng.randrange(-3, 4) for a in r.free_names(formula)}
        word = r.factor_names(mapping)
        expected = r.encode(r.rename(formula, lambda a: mapping[a]))
        assert r.apply_word(word, r.encode(formula)) == expected
        composed_stream_cases += 1

    detected_mutations = 0
    for mode, table in tables.items():
        assert len(witnesses[mode]) == len(table["rows"])
        for q, bit, _, _ in table["rows"]:
            bits, expected = witnesses[mode][q, bit]
            actual, _ = run_table(table, bits, (q, bit))
            assert actual != expected
            detected_mutations += 1

    invalid_rejections = 0
    for bits in ("", "0", "0000", "11", "110000", "101101000", "2", "01100"):
        try:
            r.decode(bits)
        except ValueError:
            invalid_rejections += 1
        else:
            raise AssertionError(("invalid fixture unexpectedly valid", bits))

    certificate_path = output_dir / "stream_transducers.json"
    certificate_path.write_text(json.dumps(tables, indent=2) + "\n")
    result = {
        "status": "finite tests passed; all-input proof is in the report",
        "binary_turing_machine_claim": False,
        "transducer_state_counts": {m: t["states"] for m, t in tables.items()},
        "formula_cases": len(formulas), "stream_map_cases": stream_cases,
        "signed_boundary_cases": scalar_cases, "conjugation_scalar_cases": conjugations,
        "finite_map_factorizations": factorizations,
        "factorization_contraction_histogram_exhaustive_part": rank_counts,
        "longest_generator_word_tested": worst_word,
        "composed_stream_cases": composed_stream_cases,
        "transition_mutations_detected": detected_mutations,
        "every_transducer_transition_has_valid_scoped_formula_witness": True,
        "invalid_syntax_fixtures_rejected": invalid_rejections,
        "source_sha256": hashlib.sha256(Path(r.__file__).read_bytes()).hexdigest(),
        "tables_sha256": hashlib.sha256(certificate_path.read_bytes()).hexdigest(),
        "seconds": round(time.monotonic() - started, 3),
    }
    (output_dir / "stream_renaming_results.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "results")
    args = parser.parse_args()
    print(json.dumps(check(args.output), indent=2))
