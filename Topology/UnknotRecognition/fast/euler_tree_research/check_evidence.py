"""Replay retained Euler-tree evidence without surface discovery or new timings.

The saved Regina lists and quotient observations remain finite oracle evidence;
this checker validates their coordinates and comparisons without importing
Regina or claiming to reconstruct the completeness of an oracle enumeration.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from math import gcd, isfinite
from random import Random
from statistics import median
from types import SimpleNamespace

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.source_kernel_verify import SourceKernelVerifier
from .benchmark import (ROOT, ARMS, SEED, arm_configs, baseline_pin, encode_result,
                        load_baseline, source_hashes, verify_result)
from .fixtures import supplied_cases, diagram_cases


MODELS = ('source', 'restricted')
STRATEGIES = ('envelope', 'anchors')
DIAGRAM_CONFIG = dict(sector_method='tree', tree_model='source', lp_strategy='envelope',
                      reduce_vertices=True, max_tree_nodes=256,
                      max_pivots=10000, max_anchors=10000, max_crushes=None)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def object_digest(value):
    return sha256(encode_result(value)).hexdigest()


def positive_number(value):
    assert type(value) in (int, float) and isfinite(value) and value > 0


def support(rows):
    return [[t, q] for t, row in enumerate(rows) for q in range(3) if row[4+q]]


def restricted_kernel(prepared, rows):
    flat = tuple(value for row in rows for value in row)
    indices = tuple(j for j, value in enumerate(flat) if value)
    equations = tuple(tuple(equation.get(j, 0) for j in indices)
                      for equation in prepared['matching'])
    kernel = SourceKernelVerifier(SimpleNamespace(n=len(indices), equations=equations,
                                                   conflicts=()), cache_size=0)
    return kernel, tuple(flat[j] for j in indices)


def positive_observation(prepared, coordinates, observation, allowed=None):
    analysed = _coordinates(prepared, coordinates, lambda: None)
    rows, quads = analysed['rows'], support(analysed['rows'])
    assert quads and analysed['euler_characteristic'] > 0
    minima = {}
    for corner, vertex in enumerate(prepared['vertex_roots']):
        value = rows[corner//4][corner % 4]
        minima[vertex] = min(minima.get(vertex, value), value)
    assert not any(minima.values())
    assert observation['euler_characteristic'] == analysed['euler_characteristic']
    assert observation['vertex_link'] is False and type(observation['connected']) is bool
    assert observation['quad_support'] == quads
    # Regina uses its own global vertex numbering, so only its canonical zero
    # values and complete index range are compared with native vertex classes.
    assert observation['vertex_triangle_minima'] == [[i, 0] for i in range(len(minima))]
    if allowed is not None:
        assert set(map(tuple, quads)) <= set(map(tuple, allowed))
    return analysed


def crushing_comparison(source, comparison, expected_rows=None):
    result, oracle = comparison['native'], comparison['regina']
    assert result['status'] == 'COMPLETE'
    proof = result['certificate']
    if expected_rows is not None:
        assert proof['coordinates'] == expected_rows
    assert verify_normal_crushing(source, proof)
    assert comparison['independent_crushing_replay'] is True
    assert comparison['exact_labelled_quotient_equal'] is True
    prepared = _prepare(source, lambda: None)
    analysed = _coordinates(prepared, proof['coordinates'], lambda: None)
    rows = analysed['rows']
    count = sum(bool(value) for row in rows for value in row)
    assert oracle['eligible'] is True and oracle['connected'] is True
    assert oracle['vertex_link'] is False and oracle['euler'] == analysed['euler_characteristic']
    assert oracle['support'] == count and oracle['support_rank'] == count-1
    assert oracle['support_nullity'] == 1 and oracle['divisor'] == gcd(*(x for row in rows for x in row)) == 1
    for native, reference in (('triangulation', 'quotient'), ('components', 'components'),
                              ('torus_component', 'torus_component'), ('successor', 'successor')):
        assert proof[native] == oracle[reference], native
    return proof


def check_audit(audit, *, require_diagrams=True):
    assert audit['models'] == list(MODELS) and audit['strategies'] == list(STRATEGIES)
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
        assert set(record['results']) == set(MODELS)
        for model in MODELS:
            assert set(record['results'][model]) == set(STRATEGIES)
            for strategy in STRATEGIES:
                answer = record['results'][model][strategy]
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
    ids = [record['id'] for record in audit['diagrams']]
    assert len(set(ids)) == len(ids) and set(ids) <= set(expected_diagrams)
    if require_diagrams:
        assert set(ids) == set(expected_diagrams)
    for record in audit['diagrams']:
        diagram = expected_diagrams[record['id']]
        assert record['input_pd'] == [list(row) for row in diagram.pd]
        assert record['config'] == DIAGRAM_CONFIG
        result = record['result']
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
        else:
            prepared = _prepare(source, lambda: None)
            assert record['successor_regina'] == dict(tetrahedra=len(source['tetrahedra']),
                vertices=prepared['vertices'], valid=True, orientable=True)
        counts['diagram_'+result['status']] += 1
        counts['diagram_labelled_quotient_equal'] += len(comparisons)
    counts['oracle_sources'] = len(oracles)
    counts['original_standard_vertices'] = sum(len(oracle['vertices']) for oracle in oracles.values())
    assert dict(counts) == audit['summary']
    return counts


def check_sample(sample, result, expected_digest):
    positive_number(sample['ns'])
    assert sample['stats'] == result['stats']
    assert sample['result_bytes'] == len(encode_result(result))
    assert sample['output_sha256'] == expected_digest


def check_benchmark(benchmark):
    assert benchmark['arms'] == list(ARMS) and benchmark['configs'] == arm_configs()
    assert benchmark['seed'] == SEED
    for field in ('pairs', 'aa', 'batch'):
        assert type(benchmark[field]) is int and benchmark[field] > 0
    assert [r['id'] for r in benchmark['records']] == ['circle', 'negative_curl']
    expected = {'circle': Diagram.from_pd([]), 'negative_curl': Diagram.from_braid(2, [-1])}
    rng = Random(SEED)
    table = [r'\begin{tabular}{lrrrrrr}', r'\toprule',
             r'Case & Adaptive & Prior Q & Prior LP & Tree restricted & Tree source & A/A \\', r'\midrule']
    ratios = [('adaptive_disc', 'tree_source'), ('prior_vertex_q', 'tree_source'),
              ('prior_vertex_lp', 'tree_source'), ('tree_restricted', 'tree_source')]
    for record in benchmark['records']:
        diagram = expected[record['id']]
        assert record['input_pd'] == [list(row) for row in diagram.pd]
        assert len(record['samples']) == benchmark['pairs'] and len(record['aa_samples']) == benchmark['aa']
        assert set(record['warmup_results']) == set(record['warmup_sha256']) == set(ARMS)
        assert set(record['median_ns']) == set(ARMS)
        for arm in ARMS:
            result = record['warmup_results'][arm]
            assert result['status'] == 'UNKNOT' and verify_result(diagram, result, arm) == 'recognition'
            if arm != 'adaptive_disc':
                assert result['certificate']['status'] == 'UNKNOT'
            assert object_digest(result) == record['warmup_sha256'][arm]
            assert median(s['results'][arm]['ns'] for s in record['samples']) == record['median_ns'][arm]
        for sample in record['samples']:
            order = list(ARMS); rng.shuffle(order)
            assert sample['order'] == order and set(sample['results']) == set(ARMS)
            for arm in ARMS:
                check_sample(sample['results'][arm], record['warmup_results'][arm], record['warmup_sha256'][arm])
        assert set(record['paired_ratio']) == {f'{a}_over_{b}' for a, b in ratios}
        for left, right in ratios:
            assert median(s['results'][left]['ns']/s['results'][right]['ns']
                          for s in record['samples']) == record['paired_ratio'][f'{left}_over_{right}']
        for sample in record['aa_samples']:
            order = ['A', 'B']; rng.shuffle(order)
            assert sample['order'] == order and set(sample['results']) == {'A', 'B'}
            for value in sample['results'].values():
                check_sample(value, record['warmup_results']['adaptive_disc'], record['warmup_sha256']['adaptive_disc'])
        assert median(s['results']['A']['ns']/s['results']['B']['ns']
                      for s in record['aa_samples']) == record['aa_ratio']
        name = record['id'].replace('_', r'\_')
        values = ' & '.join(f"{record['median_ns'][arm]/1e6:.3f}" for arm in ARMS)
        table.append(f"{name} & {values} & {record['aa_ratio']:.3f} "+r'\\')
    return '\n'.join(table+[r'\bottomrule', r'\end{tabular}'])+'\n'


def check_probe(probe):
    diagrams = dict(diagram_cases())
    cases, arms = ('trefoil', 'figure_eight'), ARMS[1:]
    assert len(probe['records']) == len(cases)*len(arms)
    assert {(r['id'], r['arm']) for r in probe['records']} == {(case, arm) for case in cases for arm in arms}
    configs = arm_configs(bounded=True)
    for record in probe['records']:
        diagram, result = diagrams[record['id']], record['result']
        assert record['input_pd'] == [list(row) for row in diagram.pd]
        assert record['config'] == configs[record['arm']]
        positive_number(record['cancellation_seconds'])
        assert type(record['elapsed_ns']) is int and record['elapsed_ns'] > 0
        assert record['result_bytes'] == len(encode_result(result))
        assert record['output_sha256'] == object_digest(result)
        if result['status'] == 'CANCELLED':
            assert set(result) == {'status', 'reason'} and type(result['reason']) is str
            assert record['independent_replay'] is None and record['partial_result_returned'] is False
        else:
            assert verify_result(diagram, result, record['arm']) == record['independent_replay']
            assert record['partial_result_returned'] is (result['status'] == 'INCONCLUSIVE')
            if result['status'] == 'INCONCLUSIVE':
                assert 'certificate' not in result
            else:
                assert result['certificate']['status'] == result['status']
            if 'independent_replay_ns' in record:
                assert type(record['independent_replay_ns']) is int and record['independent_replay_ns'] > 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--publication', action='store_true')
    args = parser.parse_args()
    data = ROOT/'synthesis/data'
    audit, benchmark, probe = [json.loads((data/f'euler-tree-{name}.json').read_text())
                               for name in ('audit', 'benchmark', 'probe')]
    pins = source_hashes()
    for record in (audit, benchmark, probe):
        assert record['passed'] is True
        assert record['source_sha256'] == pins, 'source pins are missing, extra or stale'
        for name, expected in record['source_sha256'].items():
            assert digest(ROOT/name) == expected, name
    for record in (benchmark, probe):
        assert record['baseline'] == baseline_pin()
    load_baseline()
    counts = check_audit(audit)
    table = check_benchmark(benchmark)
    check_probe(probe)
    (data/'euler-tree-table.tex').write_text(table)
    if args.publication:
        assert (benchmark['pairs'], benchmark['aa'], benchmark['batch']) == (9, 3, 3)
        files = {ROOT/name for name in pins}
        files.update(data.glob('euler-tree-*'))
        for pattern in ('test*crushing*.py', 'test*euler*.py', 'test*sector*.py',
                        'test*positive_ray*.py', 'test_normal_vertex_reduction.py',
                        'test*source_kernel*.py'):
            files.update((ROOT/'fast/tests').glob(pattern))
        required = {ROOT/'fast/README.md'}
        required.update(ROOT/'synthesis'/name for name in
                        ('euler_branch_tree.tex', 'marked_cut_handlebodies.tex', 'report.pdf'))
        assert all(path.is_file() for path in required)
        files.update(required)
        target = data/'euler-tree-publication.json'
        target.write_text(json.dumps(dict(passed=True, counts=dict(counts),
            finite_complete_branching=True, fixed_source_dual_reuse=True,
            general_quasipolynomial=False, source_sha256={str(path.relative_to(ROOT)): digest(path)
            for path in sorted(files) if path.is_file() and path != target}), indent=2)+'\n')
    print('PASS', dict(counts), 'saved certificates, oracle comparisons, timing arithmetic and source pins checked')


if __name__ == '__main__':
    main()
