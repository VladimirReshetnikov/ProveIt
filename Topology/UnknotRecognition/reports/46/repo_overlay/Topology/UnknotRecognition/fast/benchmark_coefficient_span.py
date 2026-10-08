"""Randomized paired comparisons for coefficient-span and forest commutants.

The direct arm is the unchanged coefficientwise equation algorithm.  Control
uses the identical callable.  Ordering and fresh fixture construction are
outside the timers.  Every output is checked, outside timing, against the
direct arm.  Knot timers measure raw exact homology scans, not recognition's
earlier filters.  Dense coefficient fixtures are valid graded two-term
complexes and are not claimed to arise as knot prefixes.
"""
import argparse
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter

HERE = Path(__file__).resolve().parent
ROOT = HERE
sys.path.insert(0, str(ROOT))
from fastunknot import Diagram, khovanov_rank
from fastunknot import scalar_split as scalar
from fastunknot.ordering import best_scan_order
from primary_research.families import two_field_scan

SEED = 261008105
MODES = dict(direct='direct', control='direct', span='span', forest='forest')


def hashes():
    names = ['fastunknot/scalar_split.py', 'fastunknot/coefficient_span.py',
             'fastunknot/corner_split.py', 'fastunknot/primary_split.py',
             'fastunknot/recovered_grading.py', 'primary_research/families.py']
    return {name: sha256((ROOT / name).read_bytes()).hexdigest() for name in names}


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def measure(factories, summarize, rounds, batches, rng):
    expected = None
    def validate(result):
        nonlocal expected
        identity, facts = summarize(result)
        identity = digest(identity)
        if expected is None:
            expected = identity
        elif identity != expected:
            raise ArithmeticError('arms returned different exact results')
        return facts
    for factory in factories.values():
        validate(factory()())
    samples, facts = [], {}
    for _ in range(rounds):
        order = list(factories)
        rng.shuffle(order)
        times = {}
        for arm in order:
            calls = [factories[arm]() for _ in range(batches)]
            start = perf_counter()
            results = [call() for call in calls]
            times[arm] = (perf_counter() - start) / batches
            for result in results:
                facts[arm] = validate(result)
        samples.append(dict(order=order, seconds=times))
    return dict(samples=samples, median_seconds={arm: median(x['seconds'][arm] for x in samples)
        for arm in factories}, median_paired_ratios={a + '/' + b:
        median(x['seconds'][a] / x['seconds'][b] for x in samples)
        for a, b in [('direct', 'control'), ('direct', 'span'), ('direct', 'forest')]},
        identical_result_sha256=expected, facts=facts)


def solve(scan, mode):
    stats = {}
    result = scalar.scalar_endomorphism_space(scan, list(range(len(scan.mid))),
        max_variables=None, coefficient_mode=mode, coefficient_stats=stats)
    return result, stats


def summarize_solve(result):
    space, stats = result
    blocks, variables, basis, equations = space
    return (blocks, list(variables.items()), basis), dict(stats=stats,
        equations=equations, variables=len(variables), dimension=len(basis))


def capture_prefixes(diagram, order):
    snapshots = []
    original = scalar.scalar_endomorphism_space
    def capture(scan, group, **kwargs):
        space = original(scan, group, **kwargs)
        if space is not None:
            snapshots.append(scalar._View(scan, group))
        return space
    scalar.scalar_endomorphism_space = capture
    try:
        scalar.fitting_khovanov_rank(diagram.pd, order=order, fitting_primary=True)
    finally:
        scalar.scalar_endomorphism_space = original
    return snapshots


def dense_scan(degree, dot_variables, *, mode='direct', record=False):
    scan, evidence = two_field_scan(degree, mixing='dense', fitting_primary=True,
        fitting_coefficient_mode=mode, record_witnesses=record)
    dot_degree = dot_variables // 2
    masks = [sum(1 << index for index in subset)
             for subset in combinations(range(dot_variables), dot_degree)]
    left = sum(1 << mask for mask in masks if mask & 1)
    right = sum(1 << mask for mask in masks if not mask & 1)
    matching = scan.algebra.intern(tuple((2 * i, 2 * i + 1) for i in range(dot_variables)))
    scan.mid = [matching] * scan.live
    scan.points = frozenset(range(2 * dot_variables))
    for row in scan.out:
        for target, value in row.items():
            row[target] = (left if value & 2 else 0) ^ (right if value & 4 else 0)
    scan.check_d_squared()
    evidence.update(dot_variables=dot_variables, dot_degree=dot_degree,
        left_terms=left.bit_count(), right_terms=right.bit_count(),
        coefficient_ambient_bits=1 << dot_variables,
        kind='valid homogeneous algebraic complex; no classical-knot realization claimed')
    return scan, evidence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--batches', type=int, default=2)
    parser.add_argument('--dense-rounds', type=int, default=5)
    args = parser.parse_args()
    if min(args.rounds, args.batches, args.dense_rounds) < 1:
        parser.error('positive rounds and batches required')
    frozen, rng, knots, algebraic = hashes(), random.Random(SEED), [], []
    for name in ('conway', 'kinoshita_terasaka', 'hard_unknot_8',
                 'stress_braid5_36', 'torus_3_5'):
        diagram = Diagram.from_json(json.loads((ROOT / 'examples' / (name + '.json')).read_text()))
        order = best_scan_order(diagram.pd, tries=min(12, diagram.crossings))
        reference = khovanov_rank(diagram.pd, order=order)
        snapshots = capture_prefixes(diagram, order)
        def factory(mode):
            return lambda: lambda: scalar.fitting_khovanov_rank(diagram.pd, order=order,
                fitting_primary=True, fitting_coefficient_mode=mode)
        def summarize(result):
            if result['by_degree'] != reference['by_degree']:
                raise ArithmeticError('raw scan disagrees with ordinary exact homology')
            return (result['by_degree'], result['stages']), result['stats']
        raw = measure({arm: factory(mode) for arm, mode in MODES.items()},
                      summarize, args.rounds, args.batches, rng)
        row = dict(name=name, pd=diagram.pd, order=order, raw_scan=raw,
                   eligible_prefix_solves=len(snapshots))
        if snapshots:
            def prefix_factory(mode):
                return lambda: lambda: [solve(scan, mode) for scan in snapshots]
            def summarize_prefix(results):
                outputs = [summarize_solve(result) for result in results]
                return [x[0] for x in outputs], [x[1] for x in outputs]
            row['prefix_solves'] = measure({arm: prefix_factory(mode)
                for arm, mode in MODES.items()}, summarize_prefix,
                args.rounds, max(4, args.batches), rng)
        knots.append(row)
        print(name, 'raw', raw['median_seconds'],
              'prefix', row.get('prefix_solves', {}).get('median_seconds'), flush=True)
    for degree, dots in [(4, 2), (8, 2), (10, 2), (4, 8), (4, 10), (4, 12)]:
        fixture = (lambda mode='direct': two_field_scan(degree, mixing='dense',
            fitting_primary=True, fitting_coefficient_mode=mode)) if dots == 2 else (
            lambda mode='direct': dense_scan(degree, dots, mode=mode))
        initial, evidence = fixture()
        row = dict(degree=degree, dot_variables=dots, evidence=evidence,
                   objects=initial.live, differential_entries=sum(map(len, initial.out)))
        rounds = args.rounds if dots == 2 else args.dense_rounds
        batches = args.batches if dots == 2 else 1
        def factory(mode):
            def setup():
                scan, _ = fixture(mode)
                return lambda: solve(scan, mode)
            return setup
        row['solve'] = measure({arm: factory(mode) for arm, mode in MODES.items()},
            summarize_solve, rounds, batches, rng)
        def compression_factory(mode):
            def setup():
                scan, _ = fixture(mode)
                def call():
                    scan._compress([0] * scan.live)
                    return scan
                return call
            return setup
        def summarize_compression(scan):
            return (scan.mid, scan.deg, scan.out, scan.weights), scan.stats
        row['compression'] = measure({arm: compression_factory(mode)
            for arm, mode in MODES.items()}, summarize_compression, rounds, batches, rng)
        algebraic.append(row)
        print('algebraic', degree, dots, 'solve', row['solve']['median_seconds'],
              'compression', row['compression']['median_seconds'], flush=True)
    if hashes() != frozen:
        raise ArithmeticError('source changed while benchmark was running')
    result = dict(seed=SEED, rounds=args.rounds, batches=args.batches,
        dense_rounds=args.dense_rounds, python=sys.version, platform=platform.platform(),
        source_hashes=frozen, benchmark_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        baseline_commit='58ee11a97d5fd7f21647c57eefaf3ecc007931d6',
        knots=knots, algebraic=algebraic)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
