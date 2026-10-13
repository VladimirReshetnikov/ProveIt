"""Replay saved exact LP evidence, timings and publication pins; no discovery."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from math import gcd, isfinite, lcm
from pathlib import Path
from random import Random
from statistics import median

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_euler_verify import verify_sector_euler_certificate
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_crushing_search import REDUCTION_RAY
from .common import (ROOT, ARMS, SEED, MASK, Q, source_hashes, configs, diagrams,
    small_cases, bounded_cases, check_lp, check_rounding, root_leq, pairs, rational,
    encode, digest, save, verify_result)


def integer_rows(matrix, rhs):
    result = []
    for row, b in zip(matrix, rhs):
        values = list(map(rational, row))+[rational(b)]
        scale = lcm(*(value.denominator for value in values))
        integers = [int(value*scale) for value in values]
        common = 0
        for value in integers:
            common = gcd(common, abs(value))
        common = common or 1
        result.append(([value//common for value in integers[:-1]], integers[-1]//common))
    return result


def check_audit(audit, *, check_summary=True):
    counts = Counter()
    expected = small_cases()
    assert len(audit['cones']) == len(expected)
    for record, (name, matrix, objective) in zip(audit['cones'], expected):
        assert record['id'] == name
        assert record['matrix'] == [pairs(row) for row in matrix] and record['objective'] == pairs(objective)
        assert len(record['queries']) == 4
        for query, (reduce, policy) in zip(record['queries'], ((r, p) for r in (True, False) for p in ARMS)):
            options = dict(policy=policy, reduce_rows=reduce)
            if policy == 'polynomial':
                options['fast_path_pivots'] = 0
            assert query['options'] == options
            result = query['result']
            vertices = check_lp(record['matrix'], record['objective'], result, reduce_rows=reduce)
            assert record['vertices'] == [pairs(point) for point in vertices]
            stats = result['stats']
            assert stats['variables'] == len(objective) and stats['equations'] == len(matrix)
            for value in stats.values():
                assert type(value) is int and value >= 0
            if policy == 'polynomial':
                assert stats['pivots'] == stats['fast_path_pivot_limit'] == 0
                assert stats['fallback_used'] in (0, 1)
                counts['forced_fallbacks'] += stats['fallback_used']
                counts['ellipsoid_updates'] += stats['ellipsoid_iterations']
                counts['feasibility_calls'] += stats['feasibility_calls']
            counts['cone_queries'] += 1
            counts['cone_'+result['status']] += 1
        counts['cone_cases'] += 1
    assert len(audit['rounding']) == len(bounded_cases())
    for record, (name, matrix, rhs, point) in zip(audit['rounding'], bounded_cases()):
        assert record['id'] == name and record['matrix'] == [pairs(row) for row in matrix]
        assert record['rhs'] == pairs(rhs)
        assert record['exact_point'] == (None if point is None else pairs(point))
        box = [[int(j == k)*sign for j in range(3)] for k in range(3) for sign in (1, -1)]
        rows = integer_rows(matrix+box, rhs+[1]*6)
        height = max(1, *(abs(a) for row, _ in rows for a in row))
        epsilon = Q(1, 2*(4*height)**4)
        ratio = Q(6)/(epsilon/(3*height))
        exponent = 0
        while Q(2)**exponent < ratio:
            exponent += 1
        planned = 36*(exponent+1)
        decision = record['decision']
        assert decision['status'] == ('FEASIBLE' if point is not None else 'INFEASIBLE')
        assert rational(decision['epsilon']) == epsilon and decision['planned_iterations'] == planned
        assert type(record['iterations']) is int and record['iterations'] == decision['iterations']
        assert decision['precision'] == 2*decision['iterations']+13
        if point is None:
            assert all(sum(row[j] for row in matrix) == 0 for j in range(3)) and sum(rhs) < 0
            assert decision['iterations'] == planned and decision['reason'] == 'certified volume cutoff'
        else:
            assert all(sum(a*x for a, x in zip(row, point)) <= b for row, b in rows)
            relaxed = list(map(rational, decision['relaxed_point']))
            assert all(sum(a*x for a, x in zip(row, relaxed)) <= b+epsilon for row, b in rows)
        assert len(record['updates']) == 12
        old_shape = [[Q(36) if i == j else Q(0) for j in range(3)] for i in range(3)]
        old_center = [Q(0)]*3
        for step, update in enumerate(record['updates']):
            assert update['step'] == step
            assert [list(map(rational, row)) for row in update['old_shape']] == old_shape
            assert list(map(rational, update['old_center'])) == old_center
            normal = next(row for row, b in rows if sum(a*x for a, x in zip(row, old_center)) > b+epsilon)
            assert list(map(rational, update['normal'])) == normal
            assert rational(update['spectral_floor']) == Q(36, 4**(step+1))
            assert rational(update['grid']) == Q(1, 2**(2*(step+1)+13))
            check_rounding(update)
            old_shape = [list(map(rational, row)) for row in update['new_shape']]
            old_center = list(map(rational, update['new_center']))
            counts['rounding_updates_replayed'] += 1
        counts['bounded_cases'] += 1
    assert len(audit['sqrt']) == 51
    for item, (numerator, square) in zip(audit['sqrt'], ((n, s) for n in range(-8, 9)
                                        for s in (Q(1, 9), Q(2), Q(25, 4)))):
        value, ceiling = Q(numerator, 3), item['ceiling']
        assert item['value'] == pairs([value])[0] and item['square'] == pairs([square])[0]
        assert type(ceiling) is int
        assert root_leq(value, square, ceiling) and not root_leq(value, square, ceiling-1)
        counts['signed_sqrt_checks'] += 1
    assert [record['id'] for record in audit['sources']] == ['layered_two_negative', 'one_tet_positive']
    negative, positive = audit['sources']
    for record in audit['sources']:
        assert record['source_sha256'] == digest(record['source'])
        assert record['config'] == dict(lp_fast_path_pivots=0)
        assert record['result']['stats']['lp_pivots'] == 0
    assert negative['source'] == layered_torus(2)[0] and negative['allowed_types'] == MASK
    result = negative['result']
    assert result['status'] == 'NO_POSITIVE_EULER'
    assert result['certificate']['allowed_types'] == MASK
    assert result['stats']['lp_fallbacks'] > 1 and result['stats']['transversal_restarts'] > 0
    assert verify_euler_branch_tree(negative['source'], result['certificate'])
    counts['negative_source_tree_replays'] += 1
    circle = Diagram.from_pd([])
    assert positive['input_pd'] == [] and positive['allowed_types'] == [[0, 2]]
    chain = positive['source_chain']
    assert verify_crushing_chain(circle, chain)
    assert len(chain['steps']) == 1 and chain['steps'][0]['coordinates'] == REDUCTION_RAY
    assert chain['triangulation'] == positive['source'] and len(positive['source']['tetrahedra']) == 1
    result = positive['result']
    assert result['status'] == 'POSITIVE_EULER' and result['stats']['lp_fallbacks'] == 1
    assert result['certificate']['allowed_types'] == [[0, 2]]
    assert verify_sector_euler_certificate(positive['source'], result['certificate'])
    assert result['coordinates'] == result['certificate']['coordinates']
    assert result['euler_characteristic'] == result['certificate']['euler_characteristic']
    prepared = _prepare(positive['source'], lambda: None)
    original = _coordinates(prepared, result['coordinates'], lambda: None)
    extracted = _coordinates(prepared, positive['extraction']['coordinates'], lambda: None)
    assert extracted['euler_characteristic'] > 0
    assert all(a or not b for left, right in zip(original['rows'], extracted['rows']) for a, b in zip(left, right))
    completed = positive['crushing_chain']
    assert completed['shelling'] == chain['shelling'] and completed['steps'][:1] == chain['steps']
    assert len(completed['steps']) == 2 and completed['steps'][1]['coordinates'] == positive['extraction']['coordinates']
    assert completed['triangulation'] is None and verify_crushing_chain(circle, completed)
    counts['positive_source_replays'] += 1
    counts['authenticated_chains_replayed'] += 2
    if check_summary:
        assert audit['summary'] == dict(counts)
    return dict(counts)


def check_benchmark(benchmark):
    assert benchmark['arms'] == list(ARMS) and benchmark['configs'] == configs()
    assert benchmark['seed'] == SEED
    for field in ('pairs', 'aa', 'batch'):
        assert type(benchmark[field]) is int and benchmark[field] > 0
    expected = diagrams()
    assert [r['id'] for r in benchmark['records']] == [name for name, _ in expected]
    rng = Random(SEED)
    table = [r'\begin{tabular}{lrrrr}', r'\toprule',
             r'Case & Bland (ms) & Polynomial (ms) & Bland/polynomial & A/A \\', r'\midrule']
    for record, (name, diagram) in zip(benchmark['records'], expected):
        assert record['input_pd'] == [list(row) for row in diagram.pd]
        assert set(record['warmup_results']) == set(record['warmup_sha256']) == set(ARMS)
        assert len(record['samples']) == benchmark['pairs'] and len(record['aa_samples']) == benchmark['aa']
        for arm in ARMS:
            result = record['warmup_results'][arm]
            assert result['status'] == ('UNKNOT' if name == 'circle' else 'KNOTTED')
            verify_result(diagram, result)
            assert digest(result) == record['warmup_sha256'][arm]
        left, right = [record['warmup_results'][arm] for arm in ARMS]
        identical = record['warmup_sha256']['bland'] == record['warmup_sha256']['polynomial']
        assert record['identical_full_results'] is identical
        assert record['different_top_level_fields'] == [key for key in sorted(set(left)|set(right))
                                                        if left.get(key) != right.get(key)]
        if left['stats']['lp_fallbacks'] == right['stats']['lp_fallbacks'] == 0:
            assert identical
        def check_sample(sample, arm):
            result = record['warmup_results'][arm]
            assert type(sample['elapsed_ns']) is int and sample['elapsed_ns'] > 0
            assert type(sample['ns']) in (int, float) and isfinite(sample['ns'])
            assert sample['ns'] == sample['elapsed_ns']/benchmark['batch'] > 0
            assert sample['stats'] == result['stats'] and sample['status'] == result['status']
            assert type(sample['result_bytes']) is int and sample['result_bytes'] == len(encode(result))
            assert sample['output_sha256'] == record['warmup_sha256'][arm]
        for sample in record['samples']:
            order = list(ARMS)
            rng.shuffle(order)
            assert sample['order'] == order and set(sample['results']) == set(ARMS)
            for arm in ARMS:
                check_sample(sample['results'][arm], arm)
        for sample in record['aa_samples']:
            order = ['A', 'B']
            rng.shuffle(order)
            assert sample['order'] == order and set(sample['results']) == {'A', 'B'}
            for value in sample['results'].values():
                check_sample(value, 'bland')
        medians = {arm: median(s['results'][arm]['ns'] for s in record['samples']) for arm in ARMS}
        ratio = median(s['results']['bland']['ns']/s['results']['polynomial']['ns'] for s in record['samples'])
        aa = median(s['results']['A']['ns']/s['results']['B']['ns'] for s in record['aa_samples'])
        assert record['median_ns'] == medians and record['paired_bland_over_polynomial'] == ratio and record['aa_ratio'] == aa
        table.append(name.replace('_', r'\_')+' & '+f"{medians['bland']/1e6:.3f} & {medians['polynomial']/1e6:.3f} & {ratio:.3f} & {aa:.3f}"+r' \\')
    return '\n'.join(table+[r'\bottomrule', r'\end{tabular}', ''])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, default=ROOT/'synthesis/data')
    parser.add_argument('--publication', action='store_true')
    args = parser.parse_args()
    paths = [args.data/('polynomial-lp-'+kind+'.json') for kind in ('audit', 'benchmark')]
    audit, benchmark = [json.loads(path.read_text()) for path in paths]
    pins = source_hashes()
    for evidence in (audit, benchmark):
        assert evidence['passed'] is True and evidence['source_sha256'] == pins
    summary = check_audit(audit)
    table = args.data/'polynomial-lp-table.tex'
    table.write_text(check_benchmark(benchmark))
    if args.publication:
        assert benchmark['pairs'] >= 3 and benchmark['aa'] >= 1 and benchmark['batch'] >= 1
        files = [ROOT/name for name in pins]+paths+[table]
        files += sorted((ROOT/'fast/tests').glob('test_*lp*.py'))
        files += [ROOT/name for name in ('fast/tests/test_euler_fallback_budget.py',
            'synthesis/exact_polynomial_lp.tex', 'synthesis/marked_cut_handlebodies.tex',
            'synthesis/euler_lp_crushing.tex', 'synthesis/euler_branch_tree.tex',
            'synthesis/euler_rank_replay.tex', 'synthesis/euler_transversal.tex',
            'synthesis/vertex_reduction.tex', 'synthesis/report.tex', 'synthesis/README.md',
            'synthesis/report.pdf', 'fast/README.md',
            'synthesis/data/exact-polynomial-lp-tests.txt',
            'synthesis/data/exact-polynomial-lp-regina-test.txt')]
        files += [path for name in ('polynomial-lp-latex-1.txt', 'polynomial-lp-latex-2.txt',
                                    'polynomial-lp-latex-3.txt', 'polynomial-lp-replay.txt')
                  if (path := args.data/name).exists()]
        publication = {str(path.relative_to(ROOT)): sha256(path.read_bytes()).hexdigest()
                       for path in sorted(set(files))}
        save(args.data/'polynomial-lp-publication.json', dict(passed=True, summary=summary,
            files_sha256=publication,
            scope='fresh exact finite oracle and saved-certificate replay; measured current polynomial/Bland policies; no universal admissibility-tree bound'))
    print('passed', summary)


if __name__ == '__main__':
    main()
