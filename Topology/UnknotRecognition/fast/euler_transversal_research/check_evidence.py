"""Replay transversal evidence without Regina, discovery, or new timings.

Original-STANDARD enumeration completeness remains evidence from the fresh
Regina audit; this replay verifies every retained ray and certificate. Exact
finite h claims additionally require labelled source equality, Q-extreme
positive lower witnesses, disjoint conflicts, and a complete resolving tree.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from math import isfinite
from pathlib import Path
from random import Random
from statistics import median

from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from euler_tree_research.check_evidence import (
    object_digest, support, restricted_kernel, positive_observation, crushing_comparison)
from euler_tree_research.fixtures import supplied_cases, diagram_cases
from euler_crushing_research.benchmark import encode_result, verify_result
from .benchmark import SEED, ARMS, configs, cases, expected_status
from .common import ROOT, STRATEGIES, DIAGRAM_CONFIG, source_hashes, lower_fixtures
from .formal import lower_bound_record


def check_audit(audit, *, require_diagrams=True):
    assert audit['strategies'] == list(STRATEGIES)
    assert audit['diagram_config'] == DIAGRAM_CONFIG
    oracles, prepared_sources = audit['standard_vertex_oracles'], {}
    for key, oracle in oracles.items():
        source = oracle['source']
        assert object_digest(source) == key
        prepared = _prepare(source, lambda: None)
        prepared_sources[key] = prepared
        assert prepared['vertices'] == oracle['vertex_count']
        boundary_vertices = {prepared['vertex_roots'][4*t+v]
                             for t, face in prepared['boundary_faces'] for v in range(4) if v != face}
        assert len(boundary_vertices) == oracle['boundary_vertex_count']
        vertices = oracle['vertices']
        assert len(vertices) == oracle['standard_vertex_count']
        seen = set()
        for index, vertex in enumerate(vertices):
            assert vertex['index'] == index
            analysed = _coordinates(prepared, vertex['coordinates'], lambda: None)
            rows = analysed['rows']
            encoded = tuple(x for row in rows for x in row)
            assert encoded not in seen
            seen.add(encoded)
            kernel, point = restricted_kernel(prepared, rows)
            assert kernel.verify(point, (1,)*len(point))
            assert vertex['euler_characteristic'] == analysed['euler_characteristic']
            assert vertex['quad_support'] == support(rows)
            assert vertex['vertex_link'] is (not bool(vertex['quad_support']))
            assert vertex['connected'] is True
    expected_cases = list(supplied_cases())
    assert len(audit['supplied']) == len(expected_cases)
    assert set(oracles) == {object_digest(case['source']) for case in expected_cases}
    counts = Counter()
    for record, case in zip(audit['supplied'], expected_cases):
        for field in ('id', 'family', 'mask_bits', 'allowed_types'):
            assert record[field] == case[field], (case['id'], field)
        key = object_digest(case['source'])
        assert record['source_sha256'] == key and oracles[key]['source'] == case['source']
        source, prepared = case['source'], prepared_sources[key]
        allowed = set(map(tuple, record['allowed_types']))
        targets = [v['index'] for v in oracles[key]['vertices']
                   if v['euler_characteristic'] > 0 and v['quad_support']
                   and set(map(tuple, v['quad_support'])) <= allowed]
        assert record['oracle_positive_indices'] == targets
        assert record['oracle_positive'] is bool(targets)
        counts['supplied_positive' if targets else 'supplied_negative'] += 1
        assert set(record['results']) == set(STRATEGIES)
        for strategy in STRATEGIES:
            answer = record['results'][strategy]
            result = answer['result']
            if not targets:
                assert result['status'] == 'NO_POSITIVE_EULER'
                proof = result['certificate']
                assert proof['allowed_types'] == record['allowed_types']
                assert verify_euler_branch_tree(source, proof)
                assert answer['independent_tree_replay'] is True and 'crushing' not in answer
                counts['negative_queries'] += 1
                counts['negative_tree_replays'] += 1
                counts['supplied_labelled_quotient_equal'] += 0
                continue
            assert result['status'] == 'POSITIVE_EULER'
            before = positive_observation(prepared, result['coordinates'],
                                          answer['positive_regina'], record['allowed_types'])
            assert result['euler_characteristic'] == before['euler_characteristic']
            extraction = answer['extraction']
            after = positive_observation(prepared, extraction['coordinates'],
                                         answer['extracted_regina'], record['allowed_types'])
            assert all(x or not y for old, new in zip(before['rows'], after['rows'])
                       for x, y in zip(old, new)), 'extraction grew positive support'
            matches = [v['index'] for v in oracles[key]['vertices']
                       if v['coordinates'] == extraction['coordinates']]
            assert matches == [answer['extracted_standard_vertex_index']]
            assert matches[0] in targets
            kernel, point = restricted_kernel(prepared, before['rows'])
            stats = extraction['stats']
            assert stats['matching_nullity'] == kernel.nullity
            assert stats['initial_direction_dimension'] == kernel.nullity-1
            assert type(stats['descent_steps']) is int and 0 <= stats['descent_steps'] <= kernel.nullity-1
            assert stats['input_positive_coordinates'] == len(point)
            assert stats['output_positive_coordinates'] == sum(bool(x) for row in after['rows'] for x in row)
            assert stats['source_equations'] == len(prepared['matching'])
            assert stats['input_euler_characteristic'] == before['euler_characteristic']
            assert stats['euler_characteristic'] == after['euler_characteristic']
            crushing_comparison(source, answer['crushing'], extraction['coordinates'])
            counts['positive_queries'] += 1
            counts['supplied_labelled_quotient_equal'] += 1
            counts['negative_tree_replays'] += 0
    expected_diagrams = dict(diagram_cases())
    fixtures = {item['id']: item for item in lower_fixtures()}
    ids = [record['id'] for record in audit['diagrams']]
    assert len(set(ids)) == len(ids) and set(ids) <= set(expected_diagrams)
    if require_diagrams:
        assert set(ids) == set(expected_diagrams)
    for record in audit['diagrams']:
        diagram = expected_diagrams[record['id']]
        assert record['input_pd'] == [list(row) for row in diagram.pd]
        assert record['config'] == DIAGRAM_CONFIG
        result = record['result']
        assert result['status'] == ('UNKNOT' if record['id'] == 'circle' else 'KNOTTED')
        assert verify_result(diagram, result, 'tree_source') == record['independent_verification']
        if result['status'] == 'INCONCLUSIVE':
            assert 'certificate' not in result
            chain = result['partial_chain']
        else:
            assert result['status'] in ('UNKNOT', 'KNOTTED')
            assert result['certificate']['status'] == result['status']
            chain = result['certificate']['chain']
        source = chain['shelling']['triangulation']
        comparisons = record['labelled_quotient_comparisons']
        assert len(comparisons) == len(chain['steps'])
        for packet, retained in zip(chain['steps'], comparisons):
            assert retained['source'] == source and retained['source_sha256'] == object_digest(source)
            positive_observation(_prepare(source, lambda: None), packet['coordinates'], retained['positive_regina'])
            assert crushing_comparison(source, retained['crushing']) == packet
            source = packet['successor']
        assert source == chain['triangulation']
        if source is None:
            assert record['successor_regina'] is None
            assert record['exact_transversal'] is None
        else:
            prepared = _prepare(source, lambda: None)
            assert record['successor_regina'] == dict(tetrahedra=len(source['tetrahedra']),
                vertices=prepared['vertices'], valid=True, orientable=True)
            lower = lower_bound_record(source, fixtures[record['id']])
            tree = result['certificate']['exhaustion']
            assert verify_euler_branch_tree(source, tree)
            B = sorted({node['tetrahedron'] for node in tree['nodes'] if node['kind'] == 'split'})
            assert len(B) == lower['lower_bound']
            exact = dict(lower, upper_bound=len(B), exact_h=len(B), resolving_set=B,
                negative_tree_sha256=object_digest(tree),
                witness_origin='retained rays freshly replayed; no fresh exhaustive root-ray enumeration')
            assert record['exact_transversal'] == exact
            counts['exact_transversal_instances'] += 1
            counts['positive_root_ray_replays'] += len(lower['witness_observations'])
        counts['diagram_'+result['status']] += 1
        counts['diagram_labelled_quotient_equal'] += len(comparisons)
    counts['oracle_sources'] = len(oracles)
    counts['original_standard_vertices'] = sum(len(oracle['vertices']) for oracle in oracles.values())
    assert dict(counts) == audit['summary']
    return counts


def check_sample(sample, result, expected_digest, batch):
    assert type(sample['elapsed_ns']) is int and sample['elapsed_ns'] > 0
    assert type(sample['ns']) in (int, float) and isfinite(sample['ns'])
    assert sample['ns'] == sample['elapsed_ns']/batch > 0
    assert sample['stats'] == result['stats'] and sample['status'] == result['status']
    assert sample['result_bytes'] == len(encode_result(result))
    assert sample['output_sha256'] == expected_digest


def check_benchmark(benchmark):
    assert benchmark['arms'] == list(ARMS) and benchmark['configs'] == configs()
    assert benchmark['seed'] == SEED
    for field in ('pairs', 'aa', 'batch'):
        assert type(benchmark[field]) is int and benchmark[field] > 0
    expected = cases()
    assert [record['id'] for record in benchmark['records']] == [name for name, _ in expected]
    rng = Random(SEED)
    table = [r'\begin{tabular}{lrrrrl}', r'\toprule',
             r'Case & DFS (ms) & Learning (ms) & DFS/learning & A/A & Outcomes \\', r'\midrule']
    for record, (name, diagram) in zip(benchmark['records'], expected):
        assert record['input_pd'] == [list(row) for row in diagram.pd]
        assert len(record['samples']) == benchmark['pairs']
        assert len(record['aa_samples']) == benchmark['aa']
        assert set(record['warmup_results']) == set(record['warmup_sha256']) == set(ARMS)
        assert set(record['median_ns']) == set(ARMS)
        for arm in ARMS:
            result = record['warmup_results'][arm]
            assert result['status'] == expected_status(name, arm)
            expected_replay = 'partial_chain' if result['status'] == 'INCONCLUSIVE' else 'recognition'
            assert verify_result(diagram, result, arm) == expected_replay
            assert object_digest(result) == record['warmup_sha256'][arm]
            assert median(s['results'][arm]['ns'] for s in record['samples']) == record['median_ns'][arm]
        for sample in record['samples']:
            order = list(ARMS)
            rng.shuffle(order)
            assert sample['order'] == order and set(sample['results']) == set(ARMS)
            for arm in ARMS:
                check_sample(sample['results'][arm], record['warmup_results'][arm],
                             record['warmup_sha256'][arm], benchmark['batch'])
        assert median(s['results']['tree']['ns']/s['results']['transversal']['ns']
                      for s in record['samples']) == record['paired_tree_over_transversal']
        for sample in record['aa_samples']:
            order = ['A', 'B']
            rng.shuffle(order)
            assert sample['order'] == order and set(sample['results']) == {'A', 'B'}
            for value in sample['results'].values():
                check_sample(value, record['warmup_results']['tree'],
                             record['warmup_sha256']['tree'], benchmark['batch'])
        assert median(s['results']['A']['ns']/s['results']['B']['ns']
                      for s in record['aa_samples']) == record['aa_ratio']
        escaped = name.replace('_', r'\_')
        times = ' & '.join(f"{record['median_ns'][arm]/1e6:.3f}" for arm in ARMS)
        outcomes = 'I/K' if name == 'figure_eight' else 'U/U' if name == 'circle' else 'K/K'
        table.append(f"{escaped} & {times} & {record['paired_tree_over_transversal']:.3f} & "
                     f"{record['aa_ratio']:.3f} & {outcomes} "+r'\\')
    return '\n'.join(table+[r'\bottomrule', r'\end{tabular}'])+'\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', type=Path, default=ROOT/'synthesis/data/euler-transversal-audit.json')
    parser.add_argument('--benchmark', type=Path)
    parser.add_argument('--publication', action='store_true')
    args = parser.parse_args()
    audit = json.loads(args.audit.read_text())
    pins = source_hashes()
    assert audit['passed'] is True and audit['source_sha256'] == pins, 'audit source pins stale'
    counts = check_audit(audit)
    benchmark = None
    if args.benchmark is not None:
        benchmark = json.loads(args.benchmark.read_text())
        assert benchmark['passed'] is True and benchmark['source_sha256'] == pins, 'benchmark source pins stale'
        table = check_benchmark(benchmark)
        (ROOT/'synthesis/data/euler-transversal-table.tex').write_text(table)
    assert source_hashes() == pins, 'replayed sources changed'
    if args.publication:
        assert benchmark is not None
        assert (benchmark['pairs'], benchmark['aa'], benchmark['batch']) == (5, 1, 1)
        data = ROOT/'synthesis/data'
        files = {ROOT/name for name in pins}
        files.update(data.glob('euler-transversal-*'))
        for pattern in ('test*crushing*.py', 'test*euler*.py', 'test*sector*.py',
                        'test*positive_ray*.py', 'test_normal_vertex_reduction.py',
                        'test*source_kernel*.py'):
            files.update((ROOT/'fast/tests').glob(pattern))
        required = {ROOT/'fast/README.md'}
        required.update(ROOT/'synthesis'/name for name in
                        ('euler_transversal.tex', 'marked_cut_handlebodies.tex', 'report.pdf'))
        assert all(path.is_file() for path in required)
        files.update(required)
        target = data/'euler-transversal-publication.json'
        target.write_text(json.dumps(dict(passed=True, counts=dict(counts),
            finite_complete_branching=True, finite_exact_transversal_numbers=True,
            general_quasipolynomial=False,
            source_sha256={str(path.relative_to(ROOT)): sha256(path.read_bytes()).hexdigest()
                           for path in sorted(files) if path.is_file() and path != target}), indent=2)+'\n')
    print('PASS', dict(counts), 'saved certificates, exact finite h, oracle comparisons and source pins checked')


if __name__ == '__main__':
    main()
