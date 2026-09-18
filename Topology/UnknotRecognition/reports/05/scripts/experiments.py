"""Reproduce the delivered measurements; no third-party Python packages required.

Run from the archive root: python scripts/experiments.py
"""
from __future__ import annotations

from itertools import product
import json
from pathlib import Path
import platform
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from unknot_recognition import braid_closure, recognize
from unknot_recognition.determinant import knot_determinant
from unknot_recognition.khovanov import ReducedComplex
from unknot_recognition.normal import solid_torus_example


def run():
    rows = []
    examples = (
        ('crossing-free circle', 1, [], True),
        ('positive curl', 2, [1], True),
        ('trefoil', 2, [1] * 3, False),
        ('figure-eight', 3, [1, -2] * 2, False),
        ('T(2,7)', 2, [1] * 7, False),
        ('T(3,5), determinant one', 3, [1, 2] * 5, False),
        ('R1/R2-resistant unknot', 3, [-2, -2, -2, 2, 1, 1, 2, 1], True),
    )
    for name, m, word, expected in examples:
        diagram = braid_closure(m, word)
        start = time.perf_counter()
        raw = ReducedComplex(diagram).compute(check_d_squared=True)
        raw_seconds = time.perf_counter() - start
        start = time.perf_counter()
        decision = recognize(diagram, check_d_squared=True)
        seconds = time.perf_counter() - start
        assert decision['is_unknot'] is expected
        assert (raw.total_rank == 1) is expected
        rows.append({'example': name, 'crossings': diagram.n,
                     'remaining_crossings': decision['remaining_crossings'],
                     'determinant': knot_determinant(diagram), 'F2_reduced_rank': raw.total_rank,
                     'raw_chain_basis': raw.total_basis, 'raw_resolutions': raw.resolutions,
                     'd_squared_checked': True, 'status': decision['status'],
                     'raw_seconds': raw_seconds, 'pipeline_seconds': seconds})
    # In B2, sigma_1 generates the whole braid group. The closure of word w is
    # T(2,sum(w)); for odd exponent e it is trivial exactly when abs(e)==1.
    exhaustive = 0
    start = time.perf_counter()
    for length in (1, 3, 5, 7, 9):
        for word in product((-1, 1), repeat=length):
            expected_rank = abs(sum(word))
            diagram = braid_closure(2, word)
            result = ReducedComplex(diagram).compute()
            assert result.total_rank == expected_rank, word
            assert knot_determinant(diagram) == expected_rank, word
            exhaustive += 1
    exhaustive_seconds = time.perf_counter() - start
    torus = solid_torus_example()
    multiplier = 1 << 400
    cocycle = [multiplier * x for x in torus.cocycle_basis()[0]]
    start = time.perf_counter()
    summary = torus.normal_summary(torus.normal_from_cocycle(cocycle))
    compressed_seconds = time.perf_counter() - start
    assert summary['euler_characteristic'] == multiplier
    assert summary['disks'] == 3 * multiplier
    result = {
        'environment': {'python': sys.version, 'platform': platform.platform(),
                        'processor': platform.processor()},
        'quasipolynomial_bound_established': False,
        'benchmark_warning': 'Small measurements do not establish an asymptotic bound.',
        'examples': rows,
        'exhaustive_B2': {'cases': exhaustive, 'odd_word_lengths': [1, 3, 5, 7, 9],
                          'independent_oracle': 'B2 exponent sum and the alternating torus-knot rank',
                          'seconds': exhaustive_seconds, 'all_passed': True},
        'compressed_normal_surface': {'scale': '2^400', 'tetrahedra': len(torus.tetrahedra),
                                       'coordinate_bits': summary['coordinate_bits'],
                                       'disks': '3 * 2^400', 'seconds': compressed_seconds,
                                       'connectedness_computed': False},
        'external_knot_package_cross_check': False,
        'formal_machine_checked_proof': False,
    }
    path = ROOT / 'results' / 'experiments.json'
    path.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(path)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    run()
