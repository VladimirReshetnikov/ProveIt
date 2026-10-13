"""Fresh inverse-layer replay, conditional source reductions and diagram controls.

Run from fast/ with the Regina Python environment. Outputs are evidence files,
not new immutable inputs; place them outside this package to avoid self-pins.
"""
import argparse
import json
from pathlib import Path
import platform
import sys
from time import monotonic

from fastunknot.boundary_unlayer import unlayer_boundary_once
from fastunknot.boundary_unlayer_verify import verify_boundary_unlayering
from fastunknot.normal_crushing import crush_normal_ray
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot.normal_euler_tree import search_euler_tree
from fastunknot.normal_euler_transversal import search_euler_transversal
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.positive_ray import extract_positive_ray
from .common import (digest, source_hashes, regina_triangulation, face_pairing,
                     topology_summary, SEARCH_CONFIGS, CAP_STATS, diagram_options)
from .fixtures import supplied_sources, diagram_cases

def audit_inverse_family(fixture):
    source = fixture['source']
    original = regina_triangulation(source)
    initial_topology = topology_summary(original, solid_torus=fixture['solid_torus'])
    steps = []
    while True:
        result = unlayer_boundary_once(source)
        if result['status'] == 'UNCHANGED':
            stop = result
            break
        assert result['status'] == 'UNLAYERED'
        packet = result['certificate']
        assert verify_boundary_unlayering(source, packet)
        # Regina independently deletes the actual labelled tetrahedron and
        # its incident face gluings. This does not invoke the native producer.
        oracle = regina_triangulation(source)
        oracle.removeTetrahedron(oracle.tetrahedron(packet['tetrahedron']))
        successor = packet['successor']
        assert face_pairing(oracle) == successor
        topology = topology_summary(oracle, solid_torus=fixture['solid_torus'])
        assert topology['homology'] == initial_topology['homology']
        expected = fixture.get('expected_predecessors')
        if expected is not None:
            assert successor == expected[len(steps)]
        steps.append(dict(source_sha256=digest(source), native=result,
                          regina_labelled_deletion_equal=True, regina=topology,
                          retained_predecessor_equal=expected is not None))
        source = successor
    assert len(steps) == fixture['expected_moves']
    return dict(fixture={k: v for k, v in fixture.items() if k != 'expected_predecessors'},
                initial_regina=initial_topology, steps=steps, stop=stop,
                final_source=source, final_source_sha256=digest(source),
                initial_tetrahedra=len(fixture['source']['tetrahedra']),
                final_tetrahedra=len(source['tetrahedra']))


def supplied_reduction(source, *, peel, seconds, method='dfs'):
    """Complete conditional reduction, never a diagram-authenticated verdict.

    Peeling may change existence of canonical positive normal coordinates.
    Compare the complete reduction outcomes, not just one Euler decision.
    Each positive point is extracted and crushed before restarting the query.
    """
    started = monotonic()
    current, steps, queries = source, [], []
    outcome, reason, negative = None, None, None
    outstanding_query = False
    config = SEARCH_CONFIGS[method]
    search = search_euler_tree if method == 'dfs' else search_euler_transversal

    def check():
        if monotonic()-started >= seconds:
            raise TimeoutError('per-arm exploratory wall limit exhausted')

    try:
        while current is not None:
            check()
            if peel:
                result = unlayer_boundary_once(current, check=check)
                if result['status'] == 'UNLAYERED':
                    packet = result['certificate']
                    assert verify_boundary_unlayering(current, packet, check=check)
                    steps.append(packet)
                    current = packet['successor']
                    continue
                assert result['status'] == 'UNCHANGED'
            remaining = dict(config)
            for cap, statistic in CAP_STATS.items():
                if cap in remaining:
                    remaining[cap] -= sum(q['result']['stats'].get(statistic, 0) for q in queries)
                    assert remaining[cap] >= 0
            outstanding_query = True
            answer = search(current, check=check, **remaining)
            outstanding_query = False
            queries.append(dict(source_sha256=digest(current), tetrahedra=len(current['tetrahedra']),
                                result=answer))
            if answer['status'] == 'INCONCLUSIVE':
                outcome, reason = 'INCONCLUSIVE', answer['reason']
                break
            if answer['status'] == 'NO_POSITIVE_EULER':
                negative = answer['certificate']
                assert negative['allowed_types'] == [[t, q] for t in range(len(current['tetrahedra'])) for q in range(3)]
                assert verify_euler_branch_tree(current, negative, check=check)
                outcome = 'COMPLETE_NEGATIVE_ENDPOINT'
                break
            assert answer['status'] == 'POSITIVE_EULER'
            ray = extract_positive_ray(current, answer['coordinates'], check=check)
            packet = crush_normal_ray(current, ray['coordinates'], check=check)['certificate']
            assert verify_normal_crushing(current, packet, check=check)
            steps.append(packet)
            current = packet['successor']
        if current is None:
            outcome = 'TERMINAL_NO_TORUS_COMPONENT'
    except TimeoutError as error:
        outcome, reason = 'INCONCLUSIVE', str(error)
    elapsed = monotonic()-started
    # Retained partial results receive an uncapped independent replay, even
    # after discovery's wall limit. A timeout is not a negative proof.
    replay = source
    for packet in steps:
        verify = verify_boundary_unlayering if packet['schema'] == 'normal-boundary-unlayer-v1' else verify_normal_crushing
        assert verify(replay, packet)
        assert packet['successor'] is None or len(packet['successor']['tetrahedra']) < len(replay['tetrahedra'])
        replay = packet['successor']
    assert replay == current
    if outcome == 'COMPLETE_NEGATIVE_ENDPOINT':
        assert verify_euler_branch_tree(current, negative)
    else:
        negative = None
    return dict(peel=peel, method=method, search_config=config, outcome=outcome, reason=reason,
                source=source, source_sha256=digest(source), steps=steps,
                queries=queries, final_source=current, negative_certificate=negative,
                independent_replay=True, discovery_seconds=elapsed,
                work_complete=not outstanding_query, unreturned_query=outstanding_query,
                work_scope='Counts of completed reductions and returned queries only; lower bounds if unreturned_query is true.',
                work=dict(unlayerings=sum(p['schema'] == 'normal-boundary-unlayer-v1' for p in steps),
                          crushes=sum(p['schema'] == 'normal-ray-crushing-v1' for p in steps),
                          nodes=sum(q['result']['stats']['nodes_attempted'] for q in queries),
                          pivots=sum(q['result']['stats']['lp_pivots'] for q in queries)),
                scope='Conditional supplied-source reduction only; original source must separately be authenticated as a classical knot exterior to interpret the endpoint as a knot verdict.')


def audit_diagram(name, diagram, *, scan_only=False):
    arms = {}
    for peel in (False, True):
        options = diagram_options(scan_only=scan_only, peel=peel)
        answer = recognize_by_crushing(diagram, **options)
        if answer['status'] == 'INCONCLUSIVE':
            chain = answer['partial_chain']
        else:
            assert verify_crushing_recognition(diagram, answer['certificate'])
            chain = answer['certificate']['chain']
        assert verify_crushing_chain(diagram, chain)
        final = chain['triangulation']
        faces = [] if final is None else [[t, f] for t, row in enumerate(final['tetrahedra'])
                                         for f, record in enumerate(row) if record is None]
        arms['peel' if peel else 'baseline'] = dict(options=options, result=answer,
            final_boundary_faces=faces, independent_chain_replay=True)
    if all(arm['result']['status'] != 'INCONCLUSIVE' for arm in arms.values()):
        assert arms['peel']['result']['status'] == arms['baseline']['result']['status']
    return dict(id=name, input_pd=diagram.pd, scan_only=scan_only, arms=arms)


def main():
    import regina
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--supplied-reductions', action='store_true')
    parser.add_argument('--diagrams', action='store_true')
    parser.add_argument('--diagram-scan-only', action='store_true')
    parser.add_argument('--seconds', type=float, default=20)
    args = parser.parse_args()
    assert args.seconds > 0
    pins = source_hashes()
    output = dict(schema='boundary-unlayer-research-v1', passed=False,
                  source_sha256=pins, regina=regina.versionString(), python=sys.version,
                  platform=platform.platform(), search_configs=SEARCH_CONFIGS,
                  coverage_mode='full' if args.supplied_reductions and args.diagrams and not args.diagram_scan_only else 'partial',
                  per_arm_wall_limit_seconds=args.seconds,
                  inverse_families=[], supplied_reductions=[], diagrams=[],
                  scope='Exact inverse layer replay and conditional supplied-source reductions, separated from genuine diagram recognition. Discovery wall times are diagnostic, not a benchmark.')

    def save():
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(output, indent=2)+'\n')

    for fixture in supplied_sources():
        record = audit_inverse_family(fixture)
        output['inverse_families'].append(record)
        print(fixture['id'], len(record['steps']), 'checked inverse layers', flush=True)
        save()
        if args.supplied_reductions:
            for method in SEARCH_CONFIGS:
                arms = {name: supplied_reduction(fixture['source'], peel=peel,
                            seconds=args.seconds, method=method)
                        for name, peel in (('baseline', False), ('peel', True))}
                if all(r['outcome'] != 'INCONCLUSIVE' for r in arms.values()):
                    assert arms['baseline']['outcome'] == arms['peel']['outcome']
                output['supplied_reductions'].append(dict(id=fixture['id'], method=method, arms=arms))
                print(fixture['id'], method, [(k, r['outcome'], r['work']) for k, r in arms.items()], flush=True)
                save()
    if args.diagrams or args.diagram_scan_only:
        for name, diagram in diagram_cases(extended=args.diagram_scan_only):
            record = audit_diagram(name, diagram, scan_only=args.diagram_scan_only)
            output['diagrams'].append(record)
            print(name, [(k, r['result']['status'], r['result']['stats'].get('boundary_unlayerings', 0))
                         for k, r in record['arms'].items()], flush=True)
            save()
    assert source_hashes() == pins, 'audited source changed during the run'
    output['passed'] = True
    save()
    print('PASSED', flush=True)


if __name__ == '__main__':
    main()
