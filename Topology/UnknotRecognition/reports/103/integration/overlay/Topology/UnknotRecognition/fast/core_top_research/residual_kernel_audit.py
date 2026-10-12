"""Reproduce the exact fixed-forest exceptional-row kernel evidence.

Runs finite exhaustive matrix checks, deterministic random checks, native
fixed-dual-forest cores, and the previously retained subdivision fixtures.
Literal source schedule replay imports no quotient planner in --replay-only
mode. No attached-bundle classification or knot verdict is inferred here.
"""

import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import platform
import random
import sys
import time


def literal_peel(rows):
    """Deliberately literal independent source implementation."""
    active, schedule = set(rows), []
    columns = sorted({c for row in rows.values() for c, value in row.items() if value})
    while True:
        chosen = None
        for c in columns:
            incident = [(r, rows[r].get(c, 0)) for r in sorted(active) if rows[r].get(c, 0)]
            if sum(value for _, value in incident) == 1:
                chosen = (incident[0][0], c)
                break
        if chosen is None:
            return schedule, sorted(active)
        schedule.append(list(chosen))
        active.remove(chosen[0])


def is_stopping(rows, selected):
    columns = {c for row in rows.values() for c in row}
    return all(sum(rows[r].get(c, 0) for r in selected) != 1 for c in columns)


def check_all_stopping_fibres(rows, result):
    """Brute every source stopping subset and every proposed largest lift.

    Used only for at most five rows. The hull is reconstructed independently
    by cutting each short edge, not by the producer's leaf-pruning algorithm.
    """
    labels = sorted(rows)
    exceptional = result['exceptional_rows']
    exceptional_set = set(exceptional)
    families = {}
    for mask in range(1 << len(labels)):
        selected = {r for i, r in enumerate(labels) if mask >> i & 1}
        if is_stopping(rows, selected):
            projection = tuple(sorted(selected & exceptional_set))
            families.setdefault(projection, set()).update(selected)
    adjacency, edges = {None: []}, {}
    for row in rows.values():
        for c, value in row.items():
            if value:
                adjacency.setdefault(c, [])
    for r in sorted(set(rows) - exceptional_set):
        incident = [(c, value) for c, value in rows[r].items() if value]
        assert 1 <= len(incident) <= 2 and all(value == 1 for _, value in incident)
        a = incident[0][0]
        b = incident[1][0] if len(incident) == 2 else None
        edges[r] = (a, b)
        adjacency[a].append((b, r))
        adjacency[b].append((a, r))

    def reachable(start, omitted=None):
        found, queue = {start}, [start]
        for v in queue:
            for w, edge in adjacency[v]:
                if edge != omitted and w not in found:
                    found.add(w)
                    queue.append(w)
        return found

    sides = {}
    for r, (a, b) in edges.items():
        component, side = reachable(a), reachable(a, r)
        assert b not in side
        sides[r] = (side, component - side)
    quotient_family = set()
    for mask in range(1 << len(exceptional)):
        chosen = tuple(r for i, r in enumerate(exceptional) if mask >> i & 1)
        if not is_stopping(result['quotient_rows'], chosen):
            continue
        quotient_family.add(chosen)
        marked = {None} | {c for r in chosen for c, value in rows[r].items() if value}
        hull = {r for r, (left, right) in sides.items()
                if left & marked and right & marked}
        assert families[chosen] == set(chosen) | hull
    assert set(families) == quotient_family


def check_result(rows, result):
    """Verify the elementary source claims without rebuilding the quotient."""
    _, expected = literal_peel(rows)
    assert (result['status'] == 'COMPLETE') == (not expected)
    if result['reason'] == 'short_row_cycle':
        cycle = result['short_cycle']
        assert cycle and len(cycle) == len(set(cycle)) and set(cycle) <= set(rows)
        assert is_stopping(rows, cycle)
        return
    active, used_columns = set(rows), set()
    for r, c in result['source_cancellations']:
        assert r in active and c not in used_columns
        assert rows[r].get(c, 0) == 1
        assert sum(rows[s].get(c, 0) for s in active) == 1
        active.remove(r)
        used_columns.add(c)
    assert sorted(active) == result['remaining_rows'] == expected
    assert is_stopping(rows, active)
    exceptional = result['exceptional_rows']
    assert sorted(active & set(exceptional)) == result['quotient_stopping_rows']
    _, compressed_stop = literal_peel(result['compressed_rows'])
    assert compressed_stop == result['quotient_stopping_rows']
    assert result['stats']['distinct_column_types'] <= 3 ** len(exceptional) - 1
    # Equality compression preserves the entire family of stopping subsets.
    if len(exceptional) <= 5:
        for mask in range(1 << len(exceptional)):
            chosen = [r for i, r in enumerate(exceptional) if mask >> i & 1]
            assert is_stopping(result['quotient_rows'], chosen) == is_stopping(
                result['compressed_rows'], chosen)
    if len(rows) <= 5:
        check_all_stopping_fibres(rows, result)


def sparse(matrix):
    return {r: {c: value for c, value in enumerate(row) if value}
            for r, row in enumerate(matrix)}


def restore_rows(rows):
    return {int(r): {int(c): value for c, value in row.items()} for r, row in rows.items()}


def restore_result(result):
    answer = dict(result)
    for name in ('quotient_rows', 'compressed_rows'):
        if name in answer:
            answer[name] = restore_rows(answer[name])
    return answer


def replay_only(path):
    report = json.loads(path.read_text())
    cases = report['examples'] + report['native_cases']
    for case in cases:
        check_result(restore_rows(case['occurrences']), restore_result(case['kernel']))
    print(json.dumps(dict(replayed_cases=len(cases),
                          producer_imported='core_top_research.residual_kernel' in sys.modules)))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fast-dir', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('residual_kernel_audit.json'))
    parser.add_argument('--replay-only', type=Path)
    parser.add_argument('--skip-native', action='store_true')
    args = parser.parse_args()
    if args.replay_only is not None:
        replay_only(args.replay_only)
        return
    sys.path.insert(0, str(args.fast_dir.resolve()))
    from core_top_research.residual_kernel import short_forest_kernel
    from fastunknot.integer_codec import json_safe
    started = time.perf_counter()
    counts = Counter()

    def matrix_check(rows, family, exceptional=None):
        result = short_forest_kernel(rows, exceptional_rows=exceptional)
        check_result(rows, result)
        counts[family + '_cases'] += 1
        counts[family + '_' + ('forest' if result['reason'] != 'short_row_cycle' else 'cycle')] += 1
        counts[family + '_' + result['status']] += 1
        return result

    # Every matrix with 0 <= m,n <= 3 and entries in {0,1,2}.
    for m in range(4):
        for n in range(4):
            for entries in product(range(3), repeat=m * n):
                rows = sparse([entries[r * n:(r + 1) * n] for r in range(m)])
                matrix_check(rows, 'ternary_mn_at_most_3')
    # Additional independent shape and all legal exceptional-row choices.
    for entries in product(range(2), repeat=12):
        matrix_check(sparse([entries[r * 3:(r + 1) * 3] for r in range(4)]), 'binary_4_by_3')
    for entries in product(range(2), repeat=9):
        rows = sparse([entries[r * 3:(r + 1) * 3] for r in range(3)])
        required = {r for r in rows if sum(rows[r].values()) > 2}
        for mask in range(8):
            exceptional = [r for r in range(3) if mask >> r & 1]
            if required <= set(exceptional):
                matrix_check(rows, 'all_legal_partitions_binary_3_by_3', exceptional)
    rng = random.Random(20261012)
    for _ in range(2000):
        m, n = rng.randrange(1, 10), rng.randrange(1, 10)
        rows = sparse([[rng.choices([0, 1, 2, 3, 11], [15, 12, 2, 1, 1])[0]
                        for _ in range(n)] for _ in range(m)])
        exceptional = [r for r in rows if sum(min(2, v) for v in rows[r].values()) > 2
                       or rng.randrange(3) == 0]
        matrix_check(rows, 'seeded_random', exceptional)
    high = 1 << 16384
    huge_rows = {high: {high + 1: 1, high + 2: high, high + 3: 1}}
    matrix_check(huge_rows, 'binary_multiplicity_16385_bits')
    invalid = [{True: {}}, {0: {0: True}}, {0: {0: -1}}, {0: {-1: 1}}]
    for rows in invalid:
        try:
            short_forest_kernel(rows)
        except ValueError:
            counts['invalid_inputs_rejected'] += 1
        else:
            raise ArithmeticError('invalid matrix input accepted')
    print(json.dumps(dict(stage='finite_matrix_checks_completed', counts=counts)), flush=True)

    examples = []
    named_examples = [
        ('one_long_row_three_equal_column_types', {0: {0: 1, 1: 1, 2: 1}}),
        ('grounded_component_is_not_a_pivot', {0: {0: 1}, 1: {0: 1, 1: 2}}),
        ('aggregate_two_unit_sites_in_one_tree', {0: {0: 1, 1: 1}, 1: {0: 1, 1: 1, 2: 2}}),
        ('exact_stopping_subtree_discards_branch',
         {0: {0: 1, 1: 1}, 1: {1: 1, 2: 1}, 2: {1: 1, 3: 1}, 3: {0: 1, 2: 1, 4: 2}}),
        ('quotient_pivot_cascade', {0: {0: 1, 1: 1}, 1: {1: 1, 2: 2},
                                    2: {2: 1, 3: 1, 4: 1}}),
        ('short_triangle_obstruction', {0: {0: 1, 1: 1}, 1: {1: 1, 2: 1}, 2: {0: 1, 2: 1}}),
    ]
    for name, rows in named_examples:
        result = matrix_check(rows, 'retained_examples')
        examples.append(dict(id=name, occurrences=rows, kernel=result))

    native_cases = []
    if not args.skip_native:
        from fastunknot.core_handlebody import _forest, _occurrences, capped_cancellation_plan
        from fastunknot.core_top_reduction import source_core_top_incidence, rooted_top_plan
        from fastunknot.normal_parallelity import normal_cut_parallelity

        def native_case(case, family):
            raw, coordinates = case['triangulation'], case['coordinates']
            geometry = normal_cut_parallelity(raw, coordinates)['geometry']
            incidence = source_core_top_incidence(raw, coordinates, geometry)
            core = geometry['core']
            primal, _ = _forest(core, lambda: None)
            all_rows = _occurrences(core, primal, lambda: None)
            moves, retained, _ = rooted_top_plan(incidence)
            rows = {r: all_rows[r] for r in retained}
            result = matrix_check(rows, family)
            baseline = capped_cancellation_plan(rows)
            _, literal_stop = literal_peel(rows)
            # The maintained producer permits positive nonleaf pivots, so its
            # surviving source labels need not equal the canonical no-fill
            # stopping set. Here only its complete/incomplete verdict agrees.
            if bool(baseline['remaining_rows']) != bool(literal_stop):
                raise ArithmeticError('maintained and literal raw completeness disagree')
            if not literal_stop:
                counts[family + '_ordinary_core_complete'] += 1
            native_cases.append(dict(id=case['id'], family=family,
                                     source_sha256=incidence['input_sha256'],
                                     tetrahedra=len(raw['tetrahedra']),
                                     core_handles=[len(core['handles' + str(i)]) for i in range(4)],
                                     fixed_primal_forest=primal,
                                     fixed_dual_cancellations=moves,
                                     occurrences=rows, kernel=result,
                                     literal_stopping_rows=literal_stop,
                                     maintained_positive_pivot_remaining_rows=baseline['remaining_rows'],
                                     source_schedule_replayed=True))

        corpus = json.loads((args.fast_dir / 'marked_parallelity_research/corpus.json').read_text())['cases']
        for case in corpus:
            native_case(case, 'corpus')
        subdivision_file = args.fast_dir / 'core_top_research/forest_exchange_audit.json'
        subdivisions = json.loads(subdivision_file.read_text())
        for record in subdivisions['cases']:
            if record['family'] == 'subdivision':
                native_case(record['source'], 'subdivision')

    report = dict(
        scope='exact fixed-forest raw occurrence quotient; core-only, no bundle or knot verdict',
        claim='preserves full peeling and lifts the canonical stopping set when the short graph is a forest',
        stronger_finite_check='for at most five rows, enumerate every source stopping subset; '
                              'compare its exceptional projection and the exact largest lift '
                              'against independently cut short-tree edges',
        runtime_claim='none; original explicit-matrix column peeling is already linear in sparse input size',
        python=platform.python_version(), random_seed=20261012,
        finite_domain='all {0,1,2} matrices with each dimension at most 3; all binary 4 by 3; '
                      'all legal exceptional partitions of all binary 3 by 3; 2000 seeded matrices',
        counts=counts, seconds=time.perf_counter() - started,
        native_fixed_forests='maintained core_handlebody._forest and ordinary rooted_top_plan',
        examples=examples, native_cases=native_cases)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(report), indent=2) + '\n')
    print(json.dumps(dict(counts=counts, seconds=report['seconds'])), flush=True)


if __name__ == '__main__':
    main()
