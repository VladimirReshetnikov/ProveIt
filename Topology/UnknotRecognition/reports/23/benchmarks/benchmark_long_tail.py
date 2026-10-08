"""Seeded, paired raw-homology comparison with an uncompressed A/A arm.

All three arms start from the same supplied signed runs, without word
simplification, cached homology, or a cheap recognition decision.  Input
construction is outside the timers; complex construction and rank work are
inside.  The finite-cap arm additionally checks A^2=0.  Every timed answer is
compared in every nonzero homological degree.  These are homology timings:
the source recognition filters already decide all dominant-run knots here.
"""
import argparse
import hashlib
import inspect
import json
import platform
import random
import sys
from pathlib import Path
from statistics import median
from time import perf_counter

BUNDLE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BUNDLE_ROOT / "implementation" / "fast"))

from fastunknot.twist.core import Budget, Run, homology
from fastunknot.twist.long_tail import (
    materialize_profile, tail_homology, dominant_run_obstruction,
)


def budget():
    return Budget(max_states=2_000_000, max_basis=4_000_000,
                  max_matrix_bits=4_000_000_000, max_xors=100_000_000,
                  seconds=60)


def cases():
    result = []
    for magnitude in (51, 201, 801, 4097):
        result.append(('two_strand', 2, 0, [Run(1, magnitude)], magnitude, 1))
    context4 = [Run(2, -1), Run(1, 1), Run(2, 1), Run(3, 1),
                Run(2, -1), Run(1, 1), Run(3, -1)]
    context5 = [Run(3, -1), Run(2, -1), Run(4, -1), Run(2, -1),
                Run(3, 1), Run(2, -1), Run(1, 1), Run(4, 1)]
    for name, b, selected, context in [('four_strand', 4, 3, context4),
                                        ('five_strand', 5, 6, context5)]:
        for sign in (1, -1):
            for magnitude in (51, 201, 801):
                runs = list(context)
                runs[selected] = Run(runs[selected].generator, sign * magnitude)
                result.append((name, b, selected, runs, magnitude, sign))
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--output', default=str(Path(__file__).with_name('long_tail_benchmark.json')))
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('--rounds must be positive')
    rng = random.Random(2026100801)
    records = []
    result = {
        'python': platform.python_version(), 'platform': platform.platform(),
        'kernel_sha256': hashlib.sha256(Path(inspect.getsourcefile(tail_homology)).read_bytes()).hexdigest(),
        'benchmark_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'seed': 2026100801, 'rounds': args.rounds,
        'timed_operation': 'raw reduced F2 homology with quantum grading forgotten',
        'A_A_control': 'second independent uncapped macro computation',
        'caveat': 'shared virtual environment; recognition filters already decide these knots',
        'records': records,
    }
    for name, b, selected, runs, magnitude, sign in cases():
        timings = {'macro': [], 'cap': [], 'macro_AA': []}
        last = {}
        for _ in range(args.rounds):
            arms = ['macro', 'cap', 'macro_AA']
            rng.shuffle(arms)
            profiles = {}
            for arm in arms:
                start = perf_counter()
                if arm == 'cap':
                    value = tail_homology(b, runs, selected=selected, budget=budget())
                else:
                    value = homology(b, runs, budget=budget())
                elapsed = perf_counter() - start
                timings[arm].append(elapsed)
                profiles[arm] = (materialize_profile(value['compact_by_degree'])
                                 if arm == 'cap' else value['by_degree'])
                last[arm] = value
            if not profiles['macro'] == profiles['cap'] == profiles['macro_AA']:
                raise AssertionError('a timed full homological profile disagrees')
        paired_speedups = [a / c for a, c in zip(timings['macro'], timings['cap'])]
        paired_controls = [a / c for a, c in zip(timings['macro'], timings['macro_AA'])]
        record = {
            'family': name, 'strands': b, 'selected': selected,
            'magnitude': magnitude, 'sign': sign,
            'runs': [[r.generator, r.exponent] for r in runs],
            'components': last['cap']['components'],
            'total_reduced_rank': last['cap']['reduced_rank'],
            'compact_profile': last['cap']['compact_by_degree'],
            'full_degree_agreement_in_all_rounds': True,
            'timings_seconds': timings,
            'median_paired_speedup': median(paired_speedups),
            'median_AA_ratio': median(paired_controls),
            'macro_stats': last['macro']['stats'],
            'cap_stats': last['cap']['stats'],
            'calibration': last['cap']['calibration'],
        }
        records.append(record)
        with open(args.output, 'w') as stream:
            json.dump(result, stream, indent=2)
            stream.write('\n')
        print(name, sign * magnitude, 'rank', record['total_reduced_rank'],
              'speedup', round(record['median_paired_speedup'], 3),
              'AA', round(record['median_AA_ratio'], 3), flush=True)

    huge = []
    magnitude = 10**100 + 1
    for sign in (1, -1):
        runs = [Run(2, -1), Run(1, 1), Run(2, 1), Run(3, sign * magnitude),
                Run(2, -1), Run(1, 1), Run(3, -1)]
        answer = tail_homology(4, runs, selected=3, budget=budget(), check_d2=True)
        huge.append({'runs': [[r.generator, r.exponent] for r in runs],
                     'homology': answer,
                     'dominance': dominant_run_obstruction(4, runs, selected=3)})
    result['huge_exact_examples'] = huge
    with open(args.output, 'w') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')


if __name__ == '__main__':
    main()
