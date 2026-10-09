"""Paired macro/tail exact-homology benchmark, including controls.

The output contains all raw A/B/A rounds. Timings are for this standalone
backend, not an optimized full-recognition pipeline. Each call starts with
fresh per-computation caches. Both algorithms compute the complete reduced
homology; tail uses a compressed degree-profile representation.
"""
from __future__ import annotations

import hashlib
import json
import platform
import statistics
import sys
from pathlib import Path
from time import perf_counter

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

from fastunknot.twist import core
from fastunknot.twist.core import Run, homology
from fastunknot.twist.tail import expand_profile, tail_homology


def timed(function):
    start = perf_counter()
    result = function()
    return perf_counter()-start, result


def paired_case(name, strands, runs, index, repeats=7):
    def a():
        return homology(strands, runs)

    def b():
        return tail_homology(strands, runs, run_index=index)

    original = a()
    compressed = b()
    if original['by_degree'] != expand_profile(compressed['degree_profile']):
        raise AssertionError('benchmark profiles disagree')
    rounds = []
    for round_index in range(repeats):
        before, aa = timed(a)
        tail, bb = timed(b)
        after, ac = timed(a)
        if aa['reduced_rank'] != bb['reduced_rank'] or aa['by_degree'] != ac['by_degree']:
            raise AssertionError('benchmark ranks disagree')
        rounds.append({
            'round': round_index, 'a_before_seconds': before,
            'b_seconds': tail, 'a_after_seconds': after,
            'a_mean_over_b': ((before+after)/2)/tail,
            'a_after_over_a_before': after/before,
        })
    return {
        'name': name, 'strands': strands,
        'runs': [[r.generator, r.exponent] for r in runs],
        'selected': index, 'crossings': sum(abs(r.exponent) for r in runs),
        'components': original['components'],
        'rank': original['reduced_rank'],
        'baseline_basis': original['stats']['basis'],
        'reference_basis': compressed['reference']['stats']['basis'],
        'baseline_macro_states': original['stats']['macro_states'],
        'reference_macro_states': compressed['reference']['stats']['macro_states'],
        'baseline_matrix_bit_upper_bound': original['stats']['matrix_bit_upper_bound'],
        'reference_matrix_bit_upper_bound': compressed['reference']['stats']['matrix_bit_upper_bound'],
        'method': compressed['method'],
        'profile_points': len(compressed['degree_profile']['points']),
        'profile_intervals': len(compressed['degree_profile']['intervals']),
        'median_a_mean_over_b': statistics.median(r['a_mean_over_b'] for r in rounds),
        'median_a_after_over_a_before': statistics.median(r['a_after_over_a_before'] for r in rounds),
        'rounds': rounds,
    }


def main():
    cases = []
    for m in (17, 65, 257, 1025):
        cases.append((f'two_strand_{m}', 2, [Run(1, m)], 0))
        cases.append((f'figure_eight_context_{m}', 3,
                      [Run(1, m), Run(2, -1), Run(1, 1), Run(2, -1)], 0))
        cases.append((f'four_strand_mixed_{m}', 4,
                      [Run(1, m), Run(2, -1), Run(3, 1), Run(2, -1)], 0))
    cases.append(('no_compression_control', 3,
                  [Run(1, 1), Run(2, -1), Run(1, 1), Run(2, -1)], 0))
    output = {
        'python': sys.version, 'platform': platform.platform(),
        'repository_parent_commit': '8126705bcb003b1082f117c87e4af7136b1d2c43',
        'baseline_core_sha256': hashlib.sha256(Path(core.__file__).read_bytes()).hexdigest(),
        'tail_sha256': hashlib.sha256((ROOT / 'fastunknot' / 'twist' / 'tail.py').read_bytes()).hexdigest(),
        'repeats': 7, 'protocol': 'fresh caches; one warm A/B pair; seven A/B/A rounds',
        'scope': 'standalone exact reduced homology; not end-to-end knot recognition',
        'records': [],
    }
    for args in cases:
        record = paired_case(*args)
        output['records'].append(record)
        print(json.dumps({
            'case': record['name'], 'basis_A': record['baseline_basis'],
            'basis_B': record['reference_basis'],
            'median_A_over_B': record['median_a_mean_over_b'],
        }), flush=True)
    # Separate identical-algorithm A/A noise control on the same largest
    # nontrivial-context input, without inserting a tail call between the pair.
    control_runs = [Run(1, 1025), Run(2, -1), Run(1, 1), Run(2, -1)]
    aa = []
    for j in range(7):
        first, _ = timed(lambda: homology(3, control_runs))
        second, _ = timed(lambda: homology(3, control_runs))
        aa.append({'round': j, 'first_seconds': first, 'second_seconds': second,
                   'second_over_first': second/first})
    output['separate_a_a_control'] = aa
    (Path(sys.argv[1])).write_text(
        json.dumps(output, indent=2)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
