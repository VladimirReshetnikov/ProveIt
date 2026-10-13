"""Independent retained-evidence replay; imports no inverse or LP producer."""
import argparse
import json
from math import isfinite
from pathlib import Path

from fastunknot.diagram import Diagram
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.boundary_unlayer_verify import verify_boundary_unlayering
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import verify_crushing_recognition
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from .common import (source_hashes, digest, regina_triangulation, face_pairing,
                     topology_summary, SEARCH_CONFIGS, CAP_STATS, diagram_options)
from .fixtures import supplied_sources, diagram_cases


def replay_steps(source, steps):
    current, sources = source, {digest(source): source}
    for packet in steps:
        assert current is not None
        assert packet['schema'] in ('normal-boundary-unlayer-v1', 'normal-ray-crushing-v1')
        verify = verify_boundary_unlayering if packet['schema'] == 'normal-boundary-unlayer-v1' else verify_normal_crushing
        assert verify(current, packet)
        following = packet['successor']
        assert following is None or len(following['tetrahedra']) < len(current['tetrahedra'])
        if following is not None:
            sources[digest(following)] = following
        current = following
    return current, sources


def replay_reduction(record):
    assert record['independent_replay'] is True
    assert type(record['discovery_seconds']) in (int, float) and isfinite(record['discovery_seconds']) and record['discovery_seconds'] >= 0
    assert record['method'] in SEARCH_CONFIGS and record['search_config'] == SEARCH_CONFIGS[record['method']]
    source = record['source']
    assert digest(source) == record['source_sha256']
    current, sources = replay_steps(source, record['steps'])
    assert current == record['final_source']
    assert type(record['unreturned_query']) is bool
    assert type(record['work_complete']) is bool
    assert record['work_complete'] is (not record['unreturned_query'])
    if record['unreturned_query']:
        assert record['outcome'] == 'INCONCLUSIVE' and 'wall limit' in record['reason']
    work = dict(unlayerings=sum(p['schema'] == 'normal-boundary-unlayer-v1' for p in record['steps']),
                crushes=sum(p['schema'] == 'normal-ray-crushing-v1' for p in record['steps']),
                nodes=sum(q['result']['stats']['nodes_attempted'] for q in record['queries']),
                pivots=sum(q['result']['stats']['lp_pivots'] for q in record['queries']))
    assert all(type(v) is int and v >= 0 for v in record['work'].values())
    assert work == record['work']
    for query in record['queries']:
        assert all(type(v) is int and v >= 0 for v in query['result']['stats'].values())
        assert type(query['tetrahedra']) is int and query['tetrahedra'] > 0
    for cap, statistic in CAP_STATS.items():
        if cap in record['search_config']:
            assert all(statistic in q['result']['stats'] for q in record['queries'])
            assert sum(q['result']['stats'][statistic] for q in record['queries']) <= record['search_config'][cap]
    for query in record['queries']:
        query_source = sources[query['source_sha256']]
        assert len(query_source['tetrahedra']) == query['tetrahedra']
        answer = query['result']
        if answer['status'] == 'NO_POSITIVE_EULER':
            packet = answer['certificate']
            assert packet['allowed_types'] == [[t, q] for t in range(query['tetrahedra']) for q in range(3)]
            assert verify_euler_branch_tree(query_source, packet)
        elif answer['status'] == 'POSITIVE_EULER':
            p = _prepare(query_source, lambda: None)
            observation = _coordinates(p, answer['coordinates'], lambda: None)
            assert observation['euler_characteristic'] == answer['euler_characteristic'] > 0
            minima = {}
            for t, row in enumerate(observation['rows']):
                for v in range(4):
                    root = p['vertex_roots'][4*t+v]
                    minima[root] = min(minima.get(root, row[v]), row[v])
            assert not any(minima.values())
        else:
            assert answer['status'] == 'INCONCLUSIVE'
    if record['outcome'] == 'TERMINAL_NO_TORUS_COMPONENT':
        assert current is None
        assert record['reason'] is None and record['negative_certificate'] is None
    elif record['outcome'] == 'COMPLETE_NEGATIVE_ENDPOINT':
        assert current is not None
        assert record['reason'] is None and record['work_complete'] is True
        packet = record['negative_certificate']
        assert packet['allowed_types'] == [[t, q] for t in range(len(current['tetrahedra'])) for q in range(3)]
        assert verify_euler_branch_tree(current, packet)
    else:
        assert record['outcome'] == 'INCONCLUSIVE' and record['reason']
        assert record['negative_certificate'] is None and current is not None
    return True


def replay(data, *, with_regina=False, allow_partial=False):
    pins = source_hashes()
    assert data['schema'] == 'boundary-unlayer-research-v1'
    assert data['passed'] is True and data['source_sha256'] == pins
    assert data['search_configs'] == SEARCH_CONFIGS
    assert type(data['per_arm_wall_limit_seconds']) in (int, float) and isfinite(data['per_arm_wall_limit_seconds']) and data['per_arm_wall_limit_seconds'] > 0
    assert data['coverage_mode'] in ('full', 'partial')
    assert allow_partial or data['coverage_mode'] == 'full'
    fixtures = {f['id']: f for f in supplied_sources()}
    assert [r['fixture']['id'] for r in data['inverse_families']] == list(fixtures)
    layers = 0
    for record in data['inverse_families']:
        fixture = fixtures[record['fixture']['id']]
        assert record['fixture'] == {k: v for k, v in fixture.items() if k != 'expected_predecessors'}
        source = fixture['source']
        assert _prepare(source, lambda: None)['vertices'] == 1
        assert record['initial_regina']['valid'] is True and record['initial_regina']['orientable'] is True
        if with_regina:
            assert topology_summary(regina_triangulation(source), solid_torus=fixture['solid_torus']) == record['initial_regina']
        assert len(record['steps']) == fixture['expected_moves']
        for i, step in enumerate(record['steps']):
            assert digest(source) == step['source_sha256']
            assert step['native']['status'] == 'UNLAYERED'
            assert step['regina_labelled_deletion_equal'] is True
            assert step['regina']['valid'] is True and step['regina']['orientable'] is True
            assert step['retained_predecessor_equal'] is ('expected_predecessors' in fixture)
            packet = step['native']['certificate']
            assert verify_boundary_unlayering(source, packet)
            if with_regina:
                oracle = regina_triangulation(source)
                oracle.removeTetrahedron(oracle.tetrahedron(packet['tetrahedron']))
            source = packet['successor']
            if with_regina:
                assert face_pairing(oracle) == source
                assert topology_summary(oracle, solid_torus=fixture['solid_torus']) == step['regina']
            if 'expected_predecessors' in fixture:
                assert source == fixture['expected_predecessors'][i]
            layers += 1
        assert source == record['final_source'] and digest(source) == record['final_source_sha256']
        assert record['initial_tetrahedra'] == len(fixture['source']['tetrahedra'])
        assert record['final_tetrahedra'] == len(source['tetrahedra'])
        p = _prepare(source, lambda: None)
        assert len(source['tetrahedra']) == 1 or len({t for t, _ in p['boundary_faces']}) == 2
        assert record['stop']['status'] == 'UNCHANGED'
    keys = [(r['id'], r['method']) for r in data['supplied_reductions']]
    assert len(keys) == len(set(keys))
    if data['coverage_mode'] == 'full':
        assert keys == [(name, method) for name in fixtures for method in SEARCH_CONFIGS]
    for record in data['supplied_reductions']:
        source = fixtures[record['id']]['source']
        assert set(record['arms']) == {'baseline', 'peel'}
        for name, arm in record['arms'].items():
            assert arm['source'] == source and arm['peel'] == (name == 'peel')
            assert arm['method'] == record['method'] and arm['search_config'] == SEARCH_CONFIGS[record['method']]
            assert replay_reduction(arm)
    expected_diagrams = dict(diagram_cases(extended=any(r['scan_only'] for r in data['diagrams'])))
    ids = [r['id'] for r in data['diagrams']]
    assert len(ids) == len(set(ids))
    if data['coverage_mode'] == 'full':
        assert ids == list(expected_diagrams) and len(ids) == 3
        assert not any(r['scan_only'] for r in data['diagrams'])
    for record in data['diagrams']:
        diagram = Diagram.from_pd(record['input_pd'])
        assert diagram == expected_diagrams[record['id']]
        assert set(record['arms']) == {'baseline', 'peel'}
        for name, arm in record['arms'].items():
            assert arm['options'] == diagram_options(scan_only=record['scan_only'], peel=name == 'peel')
            assert arm['independent_chain_replay'] is True
            answer = arm['result']
            if answer['status'] == 'INCONCLUSIVE':
                chain = answer['partial_chain']
            else:
                assert verify_crushing_recognition(diagram, answer['certificate'])
                chain = answer['certificate']['chain']
            assert verify_crushing_chain(diagram, chain)
            final = chain['triangulation']
            expected_faces = [] if final is None else [[t, f] for t, row in enumerate(final['tetrahedra']) for f, r in enumerate(row) if r is None]
            assert arm['final_boundary_faces'] == expected_faces
            stats = answer['stats']
            assert all(type(v) is int and v >= 0 for v in stats.values())
            unlayers = sum(p['schema'] == 'normal-boundary-unlayer-v1' for p in chain['steps'])
            assert stats.get('boundary_unlayerings', 0) == unlayers
            assert stats['crushing_steps'] == len(chain['steps'])-unlayers
            for cap, key in (('max_tree_nodes', 'nodes_attempted'), ('max_pivots', 'lp_pivots'),
                             ('max_anchors', 'anchors_tested'), ('max_hitting_subsets', 'hitting_subsets_tested'),
                             ('max_ellipsoid_iterations', 'lp_ellipsoid_iterations'),
                             ('max_feasibility_calls', 'lp_feasibility_calls')):
                assert stats[key] <= arm['options'][cap]
            if data['coverage_mode'] == 'full':
                assert answer['status'] == ('UNKNOT' if record['id'] == 'circle' else 'KNOTTED')
    assert source_hashes() == pins
    return dict(passed=True, inverse_families=len(fixtures), inverse_steps=layers,
                supplied_comparisons=len(data['supplied_reductions']), diagrams=len(data['diagrams']),
                regina_used=with_regina, full_coverage=data['coverage_mode'] == 'full')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--regina', action='store_true')
    parser.add_argument('--allow-partial', action='store_true')
    args = parser.parse_args()
    print(json.dumps(replay(json.loads(args.input.read_text()), with_regina=args.regina,
                            allow_partial=args.allow_partial), sort_keys=True))


if __name__ == '__main__':
    main()
