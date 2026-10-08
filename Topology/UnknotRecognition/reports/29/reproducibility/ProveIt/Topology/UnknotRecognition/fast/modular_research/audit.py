"""Reproducible small-knot audit against integer shadows and independent cubes.

This is a correctness audit, not a performance benchmark. It forces every
listed auxiliary prime at every live matching, even when adaptive production
would stop earlier. Full F2 reduced cubes are exponential and restricted to at
most nine crossings. All source braids, orders, mirrors and positive replay
records are saved so that the run can be reproduced without random selection.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import random
import sys
from time import perf_counter

FAST = Path(__file__).resolve().parents[1]
ROOT = FAST.parent
sys.path[:0] = [str(FAST), str(ROOT / 'reports/26')]

from fastunknot import Diagram
from fastunknot.component_scan import ComponentScan, components
from fastunknot.modular_shadow import (ModularClosureShadow,
    component_modular_shadow_bound, modular_shadow_khovanov_decide)
from fastunknot.modular_verify import replay_modular_shadow
from fastunknot.recovered_grading import recover_shifts
from fastunknot.shadow_scan import ClosureShadow, component_shadow_bound
from detshadow.cube import reduced_homology
from detshadow.diagram import Diagram as ReferenceDiagram


PRIMES = (3, 5, 7, 11, 13, 65521)


def inputs(count, seed, max_crossings):
    rng = random.Random(seed)
    rows = []
    fixed = [('trefoil', 2, [1, 1, 1]),
             ('figure-eight', 3, [1, -2, 1, -2]),
             ('unknot-with-cancellation', 2, [1, 1, -1]),
             ('one-crossing-unknot', 2, [1]),
             ('torus-3-4', 3, [1, 2] * 4)]
    seen = set()
    for name, strands, word in fixed:
        if len(word) <= max_crossings:
            diagram = Diagram.from_braid(strands, word)
            rows.append(dict(name=name, strands=strands, word=word,
                             order=list(range(len(word))), selection='fixed'))
            seen.add(diagram.pd)
    accepted = attempts = 0
    while accepted < count:
        attempts += 1
        if attempts > max(1000, 200 * count):
            raise RuntimeError('random source selection exhausted its attempt allowance')
        strands = rng.randrange(2, 6)
        word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                for _ in range(rng.randrange(3, max_crossings + 1))]
        try:
            diagram = Diagram.from_braid(strands, word)
        except ValueError:
            continue
        if diagram.pd in seen:
            continue
        seen.add(diagram.pd)
        order = list(range(len(word)))
        rng.shuffle(order)
        rows.append(dict(name='random-%03d' % accepted, strands=strands, word=word,
                         order=order, selection='seeded-random'))
        accepted += 1
    return rows, attempts


def integer_components(scan, engine, stage):
    records, weighted = {}, 0
    for group in components(scan):
        shifts = recover_shifts(scan, group)
        vector = [0] * 4
        for vertex in group:
            value = engine.evaluate(stage, scan.algebra.pairs[scan.mid[vertex]])
            sign = -1 if scan.deg[vertex] % 2 else 1
            for j, coefficient in enumerate(value):
                vector[(j + shifts[vertex]) % 4] += sign * coefficient
        multiplicity = sum(scan.weights[scan.owner[group[0]]].values())
        norm = sum(map(abs, vector))
        weighted += multiplicity * norm
        records[tuple(group)] = dict(vector=vector, norm=norm, multiplicity=multiplicity)
    return weighted, records


def audit(rows, seed, attempts):
    start = perf_counter()
    totals = Counter(base_inputs=len(rows), prime_count=len(PRIMES))
    methods, ranks, crossing_histogram = Counter(), Counter(), Counter()
    cases = []
    for index, row in enumerate(rows):
        original = Diagram.from_braid(row['strands'], row['word'])
        for mirrored, diagram in ((False, original), (True, original.mirror())):
            context = dict(input_index=index, mirrored=mirrored, name=row['name'])
            order = row['order']
            reference = reduced_homology(ReferenceDiagram(diagram.pd),
                max_crossings=9, max_generators=250000, check_d2=True)
            rank = reference['rank']
            expected_status = 'UNKNOT' if rank == 1 else 'KNOTTED'
            totals['diagrams'] += 1
            totals['full_reduced_cubes'] += 1
            totals['cube_generators'] += reference['generators']
            totals['cube_d2_columns'] += reference['d2_columns']
            ranks[rank] += 1
            crossing_histogram[diagram.crossings] += 1
            exact = ClosureShadow(diagram.pd, order, max_states=None, max_work=None)
            modular = ModularClosureShadow(diagram.pd, order, primes=PRIMES,
                                            max_states=None, max_work=None)
            small = ModularClosureShadow(diagram.pd, order, primes=(3,),
                                          max_states=None, max_work=None)
            scan = ComponentScan(shape_cache=False, rank_cap=3)
            stage_records = []
            for stage, crossing in enumerate(order):
                totals['proper_prefixes'] += 1
                live = sorted(set(scan.mid) - {None})
                for matching in live:
                    pairs = scan.algebra.pairs[matching]
                    value = exact.evaluate(stage, pairs)
                    for prime in PRIMES:
                        actual = modular.evaluate(stage, pairs, prime)
                        assert actual == tuple(x % prime for x in value), (context, stage, prime)
                        totals['modular_vector_comparisons'] += 1
                    totals['actual_matching_completions'] += 1
                geometry = modular.boundary_geometry
                b = len(geometry.labels)
                if b:
                    assert len(geometry.terminals) * 2 == b, (context, stage, 'terminal count')
                    assert geometry.open_colors.count(0) == geometry.open_colors.count(1) == b // 2
                    totals['terminal_half_frontier_checks'] += 1
                else:
                    assert len(geometry.terminals) == 1
                    totals['empty_frontier_grounding_checks'] += 1
                totals['maximum_frontier_darts'] = max(totals['maximum_frontier_darts'], b)
                totals['maximum_terminals'] = max(totals['maximum_terminals'], len(geometry.terminals))
                for matching in live:
                    pairs = scan.algebra.pairs[matching]
                    data = modular.partitions[tuple(pairs)]
                    if data['shadow_components'] != 1:
                        totals['disconnected_completions'] += 1
                    for prime, kernel in modular.kernels.items():
                        q = len(set(data['partition'])) - 1
                        totals['maximum_residual_nullity'] = max(
                            totals['maximum_residual_nullity'], kernel.nullity)
                        if kernel.nullity <= q:
                            size = kernel.nullity + q
                            assert size <= (b - 2 if b else 0), (context, stage, prime, size, b)
                            totals['frontier_minus_two_dimension_checks'] += 1
                            totals['maximum_query_matrix_dimension'] = max(
                                totals['maximum_query_matrix_dimension'], size)
                        else:
                            totals['radical_dimension_zero_cases'] += 1
                integer_bound, integers = integer_components(scan, exact, stage)
                capped_exact, _ = component_shadow_bound(scan, exact, stage, cap=2)
                assert capped_exact == min(2, integer_bound), (context, stage, 'exact component aggregate')
                assert integer_bound <= rank, (context, stage, integer_bound, rank)
                lower, records = component_modular_shadow_bound(scan, modular, stage, cap=2)
                assert 0 <= lower <= capped_exact <= min(2, rank), (context, stage, lower, capped_exact, rank)
                totals['component_bound_comparisons'] += 1
                totals['bounds_checked_against_full_homology'] += 1
                for record in records:
                    exact_record = integers[tuple(record['objects'])]
                    assert tuple(x % record['modulus'] for x in exact_record['vector']) == tuple(record['residues'])
                    assert record['norm'] <= exact_record['norm']
                    assert record['multiplicity'] == exact_record['multiplicity']
                    assert sum(exact_record['vector']) == record['exact_euler']
                    assert max(map(abs, exact_record['vector'])) <= record['coordinate_bound']
                    totals['whole_component_record_checks'] += 1
                observation = dict(modular.last_observation)
                if observation['threshold_exact']:
                    assert lower == capped_exact, (context, stage, 'exact threshold', lower, capped_exact)
                    totals['certified_threshold_agreements'] += 1
                else:
                    totals['unresolved_threshold_observations'] += 1
                small_lower, _ = component_modular_shadow_bound(scan, small, stage, cap=2)
                assert small_lower <= capped_exact, (context, stage, 'small-prime false positive')
                totals['small_prime_bound_comparisons'] += 1
                if small.last_observation['threshold_exact']:
                    assert small_lower == capped_exact
                    totals['small_prime_certified_threshold_agreements'] += 1
                if small_lower < 2 <= capped_exact:
                    assert not small.last_observation['threshold_exact']
                    totals['small_prime_missed_obstructions'] += 1
                stage_records.append(dict(stage=stage, frontier_darts=b,
                    terminals=len(geometry.terminals), live_matchings=len(live),
                    exact_weighted_bound=integer_bound, modular_bound_capped=lower,
                    small_prime_bound_capped=small_lower,
                    threshold_exact=observation['threshold_exact'],
                    used_primes=observation['primes'], modulus=observation['modulus']))
                scan.add_crossing(diagram.pd[crossing])
                scan.check_d_squared()
            assert scan.total_rank() == min(3, 2 * rank), (context, 'final capped rank')
            totals['final_capped_rank_comparisons'] += 1
            decision = modular_shadow_khovanov_decide(diagram.pd, order=order,
                shape_cache=False, euler_max_states=None, shadow_max_work=None,
                primes=PRIMES, check_d_squared=True)
            assert decision['status'] == expected_status, (context, decision['status'], rank)
            methods[decision['method']] += 1
            totals['recognition_status_comparisons'] += 1
            case = dict(**context, pd=[list(c) for c in diagram.pd], order=list(order),
                reference_reduced_homology=reference, stages=stage_records,
                decision_status=decision['status'], decision_method=decision['method'],
                decision_stage=decision['stage'])
            if decision['method'] == 'marked-residue-four-modular':
                replay = replay_modular_shadow(diagram.pd, decision)
                assert replay['verified'] and replay['verified_weighted_lower_bound'] >= 2
                assert rank > 1
                totals['positive_modular_replays'] += 1
                totals['replayed_components'] += replay['checked_components']
                case['raw_modular_claim'] = decision
                case['independent_replay'] = replay
            cases.append(case)
        if (index + 1) % 16 == 0:
            print(json.dumps(dict(completed_base_inputs=index + 1,
                                  vector_comparisons=totals['modular_vector_comparisons'],
                                  positive_replays=totals['positive_modular_replays'])), flush=True)
    assert totals['small_prime_missed_obstructions'] > 0, 'audit needs a real modular alias example'
    assert totals['positive_modular_replays'] > 0, 'audit needs a replayed obstruction'
    source_paths = [Path(__file__), FAST / 'fastunknot/modular_verify.py',
        FAST / 'fastunknot/modular_shadow.py', FAST / 'fastunknot/modular_lattice.py',
        FAST / 'fastunknot/modular_response.py', FAST / 'fastunknot/boundary_tait.py',
        FAST / 'fastunknot/boundary_connectivity.py', FAST / 'fastunknot/component_scan.py',
        FAST / 'fastunknot/scan_fast.py', FAST / 'fastunknot/recovered_grading.py',
        FAST / 'fastunknot/planar.py', FAST / 'fastunknot/shadow_scan.py',
        FAST / 'fastunknot/euler_scan.py', FAST / 'fastunknot/integer_determinant.py',
        FAST / 'fastunknot/diagram.py', FAST / 'fastunknot/frobenius/subset.py',
        FAST / 'tests/test_modular_verify.py', ROOT / 'reports/26/detshadow/cube.py',
        ROOT / 'reports/26/detshadow/diagram.py', ROOT / 'reports/26/detshadow/linalg.py']
    return dict(schema='modular-shadow-audit-v1', generated_utc=datetime.now(timezone.utc).isoformat(),
        scope=__doc__, replay_scope='Full prefix replay using the same ComponentScan and older exact integer ClosureShadow; no claim of a short standalone certificate or independently formalized scanner',
        selection=dict(seed=seed, accepted_random_inputs=sum(r['selection'] == 'seeded-random' for r in rows),
                       random_attempts=attempts, max_crossings=9,
                       mirrors_included=True, distinct_base_pd=True),
        auxiliary_primes=list(PRIMES), small_prime_palette=[3], totals=dict(totals),
        decision_methods=dict(methods), reduced_rank_histogram=dict(sorted(ranks.items())),
        crossing_histogram=dict(sorted(crossing_histogram.items())),
        elapsed_seconds=perf_counter() - start,
        sources={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in source_paths},
        base_inputs=rows, cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=FAST / 'results/modular_audit.json')
    parser.add_argument('--seed', type=int, default=26100858)
    parser.add_argument('--random-count', type=int, default=64)
    args = parser.parse_args()
    if args.random_count < 0:
        parser.error('--random-count must be nonnegative')
    rows, attempts = inputs(args.random_count, args.seed, 9)
    result = audit(rows, args.seed, attempts)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(totals=result['totals'], decision_methods=result['decision_methods'],
                          elapsed_seconds=result['elapsed_seconds']), sort_keys=True))


if __name__ == '__main__':
    main()
