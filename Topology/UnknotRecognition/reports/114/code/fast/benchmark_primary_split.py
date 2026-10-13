"""Paired primary/Fitting comparisons, with synthetic and knot scopes separate.

Knot timings include complete raw scans at a preselected common order, and
exclude Diagram construction, imports and order selection.  The synthetic
search timings include the scalar commutant solve, every candidate test,
and the complete verified basis change.  Synthetic compression timings
include recursive splitting and template sharing, but exclude fresh fixture
construction.  Synthetic components are not claimed to be knot prefixes.

All arms use fresh scan states.  Identical Fitting A/A controls and raw paired
samples are retained.  Timings do not include witness recording or audit work.
"""
import argparse
from collections import Counter
import copy
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter

from fastunknot import Diagram, khovanov_rank
from fastunknot.ordering import best_scan_order
from fastunknot.primary_split import primary_projector, verify_primary_projector
from fastunknot.scalar_split import (_fitting_bases, find_scalar_split,
    fitting_khovanov_rank)
from primary_research.families import (irreducible_pair, multiplication_matrix,
    poly_multiply, poly_remainder, two_field_scan)


SEED = 2026100809


def field_minimal_polynomial(value, modulus):
    """Independent orbit-product oracle, with coefficients multiplied in the field."""
    orbit, current = [], value
    while current not in orbit:
        orbit.append(current)
        current = poly_remainder(poly_multiply(current, current), modulus)
    if current != value:
        raise ArithmeticError('Frobenius did not act bijectively')
    coefficients = [1]
    for root in orbit:
        new = [0] * (len(coefficients) + 1)
        for i, coefficient in enumerate(coefficients):
            new[i] ^= poly_remainder(poly_multiply(coefficient, root), modulus)
            new[i + 1] ^= coefficient
        coefficients = new
    if any(value not in (0, 1) for value in coefficients):
        raise ArithmeticError('orbit product was not defined over F2')
    return sum(value << i for i, value in enumerate(coefficients))


def probability_audit():
    rows = []
    for degree in (3, 4, 5, 6):
        f, g = irreducible_pair(degree)
        q = 1 << degree
        left = [field_minimal_polynomial(value, f) for value in range(q)]
        right = [field_minimal_polynomial(value, g) for value in range(q)]
        counts_left, counts_right = Counter(left), Counter(right)
        if counts_left != counts_right:
            raise ArithmeticError('field presentations disagree on Frobenius orbits')
        failure = sum(count * count for count in counts_left.values())
        old_success = 2 * (q - 1)
        tested = 0
        if degree <= 4:
            for a in range(q):
                for b in range(q):
                    candidate = [multiplication_matrix(a, f), multiplication_matrix(b, g)]
                    projector, evidence = primary_projector(candidate)
                    expected = left[a] != right[b]
                    if (projector is not None) != expected:
                        raise ArithmeticError('primary split differs from Frobenius-orbit oracle')
                    if projector is not None:
                        verify_primary_projector(candidate, projector, evidence)
                    old_dimension = _fitting_bases([list(range(degree)), list(range(degree))],
                                                   candidate)[2]
                    if (0 < old_dimension < 2 * degree) != ((a == 0) != (b == 0)):
                        raise ArithmeticError('Fitting split differs from exact field oracle')
                    tested += 1
        distribution = Counter(polynomial.bit_length() - 1 for polynomial in counts_left)
        formula = sum(d * d * count for d, count in distribution.items())
        if formula != failure or failure > degree * q:
            raise ArithmeticError('exact probability identity failed')
        rows.append(dict(degree=degree, f=f, g=g, denominator=q*q,
                         fitting_success_numerator=old_success,
                         primary_success_numerator=q*q-failure,
                         primary_failure_numerator=failure,
                         irreducibles_by_degree=dict(distribution),
                         exact_candidate_pairs_checked=tested,
                         orbit_values_checked=2*q))
    return dict(model='independent uniform draws from F_(2^r) x F_(2^r), not production sampling',
                rows=rows)


def paired(arms, *, rounds, batches, rng):
    """An arm returns a fresh callable; setup occurs outside the timed batch."""
    samples, results = [], {}
    for arm in arms.values():
        arm()()  # Untimed warm-up.
    for _ in range(rounds):
        names = list(arms)
        rng.shuffle(names)
        times = {}
        for name in names:
            calls = [arms[name]() for _ in range(batches)]
            start = perf_counter()
            for call in calls:
                result = call()
            times[name] = (perf_counter() - start) / batches
            results[name] = result
        samples.append(dict(order=names, seconds_per_call=times))
    ratio = {name: statistics.median(sample['seconds_per_call']['fitting'] /
                                   sample['seconds_per_call'][name] for sample in samples)
             for name in arms if name != 'fitting'}
    medians = {name: statistics.median(sample['seconds_per_call'][name] for sample in samples)
               for name in arms}
    return dict(samples=samples, median_fitting_over=ratio, median_seconds=medians), results


def benchmark_knots(rounds, batches, rng):
    folder = Path(__file__).parent / 'examples'
    rows = []
    names = ('conway', 'kinoshita_terasaka', 'hard_unknot_8', 'stress_braid5_36', 'torus_3_5')
    for name in names:
        diagram = Diagram.from_json(json.loads((folder / (name + '.json')).read_text()))
        order = best_scan_order(diagram.pd, tries=min(len(diagram.pd), 12))
        reference = khovanov_rank(diagram.pd, order=order)
        def make(primary):
            def call():
                result = fitting_khovanov_rank(diagram.pd, order=order, fitting_primary=primary)
                if result['by_degree'] != reference['by_degree']:
                    raise ArithmeticError('raw scan rank disagreement')
                return result
            return call
        timing, results = paired({'fitting': lambda: make(False), 'control': lambda: make(False),
                                  'primary': lambda: make(True)}, rounds=rounds, batches=batches, rng=rng)
        diagnostic = fitting_khovanov_rank(diagram.pd, order=order, fitting_primary=True,
                                           record_witnesses=True, check_d_squared=True)
        witnesses = diagnostic['witnesses']
        for witness in witnesses:
            if 'primary' in witness:
                verify_primary_projector(witness['primary']['candidate_columns'],
                                         witness['endomorphism_columns'], witness['primary'])
        rows.append(dict(name=name, crossings=len(diagram.pd), pd=diagram.pd, order=order,
                         reference_by_degree=reference['by_degree'], timing=timing,
                         stats={arm: result['stats'] for arm, result in results.items()},
                         witnesses=witnesses))
        print('knot', name, 'F/P', round(timing['median_fitting_over']['primary'], 3),
              'A/A', round(timing['median_fitting_over']['control'], 3),
              'primary splits', results['primary']['stats']['fitting_primary_splits'], flush=True)
    return rows


def benchmark_fields(rounds, batches, rng):
    rows = []
    for degree, mixing in [(r, 'dense') for r in (3, 4, 6, 8, 10, 12)] + [(8, 'bridge')]:
        initial, fixture = two_field_scan(degree, mixing=mixing, seed=SEED)
        variable_cap = 2 * (2 * degree) ** 2
        original_entries = sum(map(len, initial.out))
        def make_search(primary):
            def call():
                rows, witness, metrics = find_scalar_split(initial, list(range(initial.live)),
                    max_variables=variable_cap, primary=primary)
                return dict(found=witness is not None, metrics=metrics, witness=witness,
                            entries_after=None if rows is None else sum(map(len, rows)))
            return call
        search_timing, search_results = paired(
            {'fitting': lambda: make_search(False), 'control': lambda: make_search(False),
             'primary': lambda: make_search(True)}, rounds=rounds, batches=batches, rng=rng)
        def make_compression(primary):
            scan, _ = two_field_scan(degree, mixing=mixing, seed=SEED, fitting_primary=primary)
            def call():
                scan._compress([0] * scan.live)
                return dict(objects=scan.live, templates=len(scan.weights),
                            entries=sum(map(len, scan.out)), stats=scan.stats)
            return call
        compression_timing, compression_results = paired(
            {'fitting': lambda: make_compression(False), 'control': lambda: make_compression(False),
             'primary': lambda: make_compression(True)}, rounds=rounds, batches=batches, rng=rng)
        witness = search_results['primary']['witness']
        if witness is not None and 'primary' in witness:
            verify_primary_projector(witness['primary']['candidate_columns'],
                                     witness['endomorphism_columns'], witness['primary'])
        rows.append(dict(degree=degree, mixing=mixing, fixture=fixture, objects=initial.live,
                         scalar_variables=variable_cap, within_default_caps=degree <= 10,
                         original_entries=original_entries,
                         search=dict(timing=search_timing, results=search_results),
                         compression=dict(timing=compression_timing, results=compression_results)))
        print('field', degree, mixing, 'search F/P', round(search_timing['median_fitting_over']['primary'], 3),
              'found', search_results['fitting']['found'], search_results['primary']['found'],
              'compression F/P', round(compression_timing['median_fitting_over']['primary'], 3), flush=True)
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--batches', type=int, default=10)
    args = parser.parse_args()
    if args.rounds < 1 or args.batches < 1:
        parser.error('rounds and batches must be positive')
    rng = random.Random(SEED)
    result = dict(scope=__doc__, python=platform.python_version(), platform=platform.platform(),
                  seed=SEED, rounds=args.rounds, batches=args.batches,
                  knots=benchmark_knots(args.rounds, args.batches, rng),
                  fields=benchmark_fields(args.rounds, args.batches, rng),
                  probabilities=probability_audit())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
