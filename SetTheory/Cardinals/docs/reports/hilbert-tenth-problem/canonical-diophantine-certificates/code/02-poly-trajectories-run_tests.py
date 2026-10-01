#!/usr/bin/env python3
"""Reproducible finite tests; the mathematical proofs are in the article."""
from __future__ import annotations
from copy import deepcopy
from dataclasses import asdict
from hashlib import sha256
from itertools import product
from math import comb
from pathlib import Path
import json
import random
import time
from certificates import (Certificate, Run, brute_runs, difference_tower,
                          evaluate, generate, padded, verify)
from quartic_compiler import compile_certificate


def sign_string_runs(values: tuple[int, ...]) -> list[Run]:
    result: list[Run] = []
    for t, value in enumerate(values):
        if result and result[-1].sign == value:
            last = result.pop()
            result.append(Run(last.start, t + 1, value))
        else:
            result.append(Run(t, t + 1, value))
    return result


def structure_digest(compiler) -> str:
    structure = [[residual.terms, label]
                 for residual, label in zip(compiler.residuals, compiler.labels)]
    return sha256(json.dumps(structure, sort_keys=True).encode()).hexdigest()


def main() -> None:
    started = time.perf_counter()
    rng = random.Random(20260930)
    random_count = 0
    for degree in range(9):
        for _ in range(180):
            coefficients = [rng.randint(-8, 8) for _ in range(degree + 1)]
            T = rng.randint(0, 60)
            certificate = generate(coefficients, T)
            assert verify(certificate)
            tower = difference_tower(coefficients)
            for k, polynomial in enumerate(tower):
                assert certificate.levels[k] == brute_runs(polynomial, T)
            assert verify(certificate, True) == all(
                evaluate(coefficients, t) >= 0 for t in range(T + 1))
            cuts, tags = padded(certificate)
            assert sum(len(b) - 2 + len(s) for b, s in zip(cuts, tags)) == (
                degree + 1) * (2 * degree + 1)
            random_count += 1

    edge_cases = [([0], 0), ([0, 0, 0, 0], 20), ([5, 0, 0, 0], 0),
                  ([-5], 10), ([0, -1, 1], 1), ([0, -1, 1], 4),
                  ([8, -6, 1], 6), ([0, 2, -3, 1], 3)]
    for coefficients, T in edge_cases:
        certificate = generate(coefficients, T)
        assert verify(certificate)
        assert certificate.levels[0] == brute_runs(coefficients, T)

    # Exhaust all potential sign tables on [0,2] for nominal degree 2.
    # Each sign string corresponds to exactly one maximal-run table.
    # This is a finite diagnostic for uniqueness, not its general proof.
    rows = [sign_string_runs(s) for s in product((-1, 0, 1), repeat=3)]
    candidate_count, uniqueness_cases = 0, 0
    for coefficients in product((-1, 0, 1), repeat=3):
        correct = generate(coefficients, 2)
        accepted = []
        for row0 in rows:
            for row1 in rows:
                for top_sign in (-1, 0, 1):
                    candidate = Certificate(list(coefficients), 2,
                        [row0, row1, [Run(0, 3, top_sign)]])
                    if verify(candidate):
                        accepted.append(candidate.levels)
                    candidate_count += 1
        assert accepted == [correct.levels]
        uniqueness_cases += 1

    mutation_count = 0
    for coefficients, T in edge_cases:
        correct = generate(coefficients, T)
        for k, row in enumerate(correct.levels):
            for j, run in enumerate(row):
                for s in (-1, 0, 1):
                    if s != run.sign:
                        mutated = deepcopy(correct)
                        mutated.levels[k][j] = Run(run.start, run.stop, s)
                        assert not verify(mutated)
                        mutation_count += 1

    # Full polynomial residual checking, including on negative instances.
    compiler_cases, false_cases = 0, 0
    reference_digests: dict[int, str] = {}
    compiler_counts = []
    for degree in range(5):
        for sample in range(10):
            coefficients = [rng.randint(-5, 5) for _ in range(degree + 1)]
            T = rng.randint(0, 15)
            certificate = generate(coefficients, T)
            compiler = compile_certificate(certificate, True)
            stats = compiler.statistics()
            assert stats['maximum_residual_degree'] <= 2
            assert stats['all_sample_witnesses_natural']
            all_nonnegative = all(evaluate(coefficients, t) >= 0 for t in range(T + 1))
            assert (not stats['failed_sample_residuals']) == all_nonnegative
            if not all_nonnegative:
                false_cases += 1
            digest = structure_digest(compiler)
            assert digest == reference_digests.setdefault(degree, digest)
            if sample == 0:
                compiler_counts.append({k: v for k, v in stats.items()
                                        if k not in ('failed_sample_residuals',)})
                compiler_counts[-1]['nominal_degree'] = degree
                compiler_counts[-1]['structure_sha256'] = digest
            compiler_cases += 1

    # Huge binary horizon: no horizon-sized enumeration.
    A, T = 10 ** 50, 10 ** 100
    huge = generate([A * A, -2 * A, 1], T)
    assert verify(huge, True)
    huge_compiler = compile_certificate(huge)
    assert not huge_compiler.statistics()['failed_sample_residuals']
    Path('huge_horizon_certificate.json').write_text(
        json.dumps(huge.to_dict(), indent=2) + '\n', encoding='utf-8')

    # Simultaneous triangular nonlinear update versus its closed form.
    loop_cases = 0
    for _ in range(100):
        a, b, c = (rng.randint(-5, 5) for _ in range(3))
        x, y, z = a, b, c
        for t in range(25):
            B = lambda j: comb(t, j) if t >= j else 0
            expected_z = (c + b*b*t + (2*a*b+a*a)*B(2)
                          + (2*a*a+2*b+4*a+1)*B(3)
                          + (6*a+6)*B(4) + 6*B(5))
            assert x == a + t
            assert y == b + a*t + B(2)
            assert z == expected_z
            x, y, z = x + 1, y + x, z + y*y
            loop_cases += 1

    # Quartic example and intentionally false endpoint-only example.
    example = generate([4, -4, 1], 6)
    example_compiler = compile_certificate(example)
    Path('quartic_example.json').write_text(
        json.dumps(example_compiler.export(), indent=2) + '\n', encoding='utf-8')
    negative_example = generate([8, -6, 1], 6)
    Path('interior_counterexample.json').write_text(
        json.dumps(negative_example.to_dict(), indent=2) + '\n', encoding='utf-8')

    report = {
        'status': 'all assertions passed', 'random_seed': 20260930,
        'random_polynomial_cases': random_count, 'edge_cases': len(edge_cases),
        'uniqueness_polynomials': uniqueness_cases,
        'exhausted_candidate_tables': candidate_count,
        'rejected_tag_mutations': mutation_count,
        'compiled_polynomial_cases': compiler_cases,
        'compiled_negative_cases': false_cases,
        'huge_horizon': str(T),
        'huge_horizon_generation_distinct_evaluations': huge.generation_evaluations,
        'huge_horizon_total_actual_sign_runs': sum(map(len, huge.levels)),
        'nonlinear_loop_state_checks': loop_cases,
        'compiler_counts': compiler_counts,
        'example_quartic': example_compiler.statistics(),
        'elapsed_seconds': round(time.perf_counter() - started, 3),
        'limitation': 'Finite executable tests are not a formal proof or an exhaustive literature audit.'
    }
    Path('test_report.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
