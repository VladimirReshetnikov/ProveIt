"""Small exact integration audit for region and diagram Pachner search.

From fast/: python -m region_research.audit --output region_research/results/audit.json
Replay: python -m region_research.audit --replay region_research/results/audit.json

This driver compares the region wrapper with a literal subset oracle, not with
the region enumerator's implementation. It also exercises a small declared
diagram cohort. Recorded elapsed time describes the audit and is not a speed
claim. No nontrivial-knot verdict is inferred from bounded-family exhaustion.
"""
import argparse
from collections import defaultdict
from datetime import datetime, timezone
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import platform
import sys
import time


FAST = Path(__file__).resolve().parents[1]
if str(FAST) not in sys.path:
    sys.path.insert(0, str(FAST))

from fastunknot.diagram import Diagram
from fastunknot.pachner_commitments_verify import verify_pachner_endpoint
from fastunknot.normal_transport_verify import verify_transport_disk_certificate


def _literal_regions(raw, maximum, components):
    """Enumerate subsets and count induced components with a plain graph walk."""
    rows = raw['tetrahedra']
    graph = [{entry['tetrahedron'] for entry in row if entry is not None}
             for row in rows]
    for size in range(min(maximum, len(rows))+1):
        for subset in combinations(range(len(rows)), size):
            remaining, count = set(subset), 0
            while remaining:
                count += 1
                queue = [remaining.pop()]
                while queue:
                    neighbours = graph[queue.pop()] & remaining
                    remaining.difference_update(neighbours)
                    queue.extend(neighbours)
            if count <= components:
                yield subset


def _certificate_set(proofs):
    """Exact certificate equality; JSON strings are compared, not just digests."""
    return {json.dumps(proof, sort_keys=True, separators=(',', ':')) for proof in proofs}


def _source_inventory():
    paths = [Path(__file__), FAST/'fastunknot'/'pachner_regions.py',
             FAST/'fastunknot'/'normal_pachner_search.py',
             FAST/'fastunknot'/'pachner_commitments.py',
             FAST/'fastunknot'/'pachner_commitments_verify.py',
             FAST/'fastunknot'/'normal_transport_verify.py']
    return {str(path.relative_to(FAST)): sha256(path.read_bytes()).hexdigest() for path in paths}


def run_audit():
    from fastunknot.normal_cocycle import rank_one_cocycle_seed
    from fastunknot.pachner_commitments import search_pachner_endpoints
    from fastunknot.pachner_regions import search_pachner_regions
    from fastunknot.normal_pachner_search import pachner_seed_decide
    from normal_orbit_research.fixtures import layered_torus
    from commitment_research.fixtures import independent_bipyramids, endpoint_keys

    started = time.perf_counter()
    cases = []
    for n, size, comp, up in ((2, 2, 1, 1), (3, 2, 1, 1)):
        raw, _ = layered_torus(n)
        h = rank_one_cocycle_seed(raw)['heights']
        cases.append((f'layered_{n}_region_{size}_components_{comp}_up_{up}',
                      raw, h, size, comp, up))
    independent = independent_bipyramids(2)
    for size, comp in ((3, 1), (3, 2), (6, 1)):
        cases.append((f'independent_2_region_{size}_components_{comp}',
                      independent['triangulation'], independent['heights'], size, comp, 0))
    records, certificate_replays, brute_calls = [], 0, 0
    for name, raw, h, size, comp, up in cases:
        common = dict(max_upward=up, max_nodes=None, seek_disc=False,
                      collect_endpoints=True, method='sleep')
        begin = time.perf_counter()
        wrapped = search_pachner_regions(raw, h, max_region_size=size,
                                          max_components=comp, **common)
        wrapper_seconds = time.perf_counter()-begin
        if wrapped['status'] != 'COMPLETE_BOUNDED_REGIONS':
            raise AssertionError((name, 'wrapper did not exhaust', wrapped['status']))
        begin = time.perf_counter()
        brute, proofs, nodes = [], [], 0
        for region in _literal_regions(raw, size, comp):
            answer = search_pachner_endpoints(raw, h,
                active_initial_tetrahedra=list(region), **common)
            if answer['status'] != 'COMPLETE_BOUNDED_FAMILY':
                raise AssertionError((name, 'brute call did not exhaust', region))
            brute.append(dict(region=list(region), result=answer))
            proofs.extend(answer['endpoints'])
            nodes += answer['stats']['nodes']
            brute_calls += 1
        brute_seconds = time.perf_counter()-begin
        if _certificate_set(wrapped['endpoints']) != _certificate_set(proofs):
            raise AssertionError((name, 'exact certificate sets differ'))
        left = endpoint_keys(raw, h, wrapped['endpoints'])
        right = endpoint_keys(raw, h, proofs)
        if left != right:
            raise AssertionError((name, 'geometric endpoint sets differ'))
        if (wrapped['stats']['regions_started'] != len(brute)
                or wrapped['stats']['regions_completed'] != len(brute)
                or wrapped['stats']['nodes'] != nodes):
            raise AssertionError((name, 'aggregate region or node count differs'))
        for proof in wrapped['endpoints']+proofs:
            if not verify_pachner_endpoint(raw, h, proof):
                raise AssertionError((name, 'endpoint proof rejected'))
            certificate_replays += 1
        records.append(dict(name=name, triangulation=raw, heights=h,
            options=dict(max_region_size=size, max_components=comp, max_upward=up),
            wrapped=wrapped, brute=brute,
            exact_certificate_sets_equal=True, geometric_endpoint_sets_equal=True,
            geometric_endpoint_count=len(left), allowed_region_count=len(brute),
            wrapper_seconds=wrapper_seconds, brute_seconds=brute_seconds))
        print(name, 'regions', len(brute), 'nodes', nodes,
              'geometric endpoints', len(left), flush=True)

    specifications = [
        ('single_crossing_unknot', 2, [1], {}, 'UNKNOT'),
        ('single_crossing_shelling', 2, [1], {'shellings': True}, 'UNKNOT'),
        ('single_crossing_empty_region', 2, [1],
         {'max_region_size': 0, 'max_components': 0}, 'UNKNOT'),
        ('cancelled_braid_unknot', 2, [1, -1, 1],
         {'shellings': True, 'max_region_size': 0}, None),
        ('trefoil_empty_region', 2, [1, 1, 1],
         {'shellings': True, 'max_region_size': 0}, 'INCONCLUSIVE'),
        ('figure_eight_empty_region', 3, [1, -2, 1, -2],
         {'shellings': True, 'max_region_size': 0}, 'INCONCLUSIVE'),
        ('single_crossing_zero_node_cap', 2, [1], {'max_nodes': 0}, 'INCONCLUSIVE'),
        ('single_crossing_zero_work_cap', 2, [1], {'max_work': 0}, 'INCONCLUSIVE'),
    ]
    diagrams, accepted, rejected_sources = [], 0, 0
    for name, strands, word, options, expected in specifications:
        diagram = Diagram.from_braid(strands, word)
        options = dict(max_nodes=10, max_work=None, **options) if not (
            'max_nodes' in options or 'max_work' in options) else dict(
                {'max_nodes': 10, 'max_work': None}, **options)
        begin = time.perf_counter()
        answer = pachner_seed_decide(diagram, **options)
        elapsed = time.perf_counter()-begin
        if expected is not None and answer['status'] != expected:
            raise AssertionError((name, expected, answer['status']))
        verified = None
        if answer['status'] == 'UNKNOT':
            verified = verify_transport_disk_certificate(diagram, answer['certificate'])
            if not verified:
                raise AssertionError((name, 'independent diagram proof rejected'))
            accepted += 1
            wrong = Diagram.from_braid(2, [1, 1, 1])
            if verify_transport_disk_certificate(wrong, answer['certificate']):
                raise AssertionError((name, 'wrong diagram accepted'))
            rejected_sources += 1
        elif answer['status'] != 'INCONCLUSIVE' or 'certificate' in answer:
            raise AssertionError((name, 'invalid bounded-negative status or proof'))
        diagrams.append(dict(name=name, braid=dict(strands=strands, word=word),
            pd=[list(row) for row in diagram.pd], options=options, result=answer,
            expected_status=expected, positive_replay=verified, elapsed_seconds=elapsed))
        print(name, answer['status'], answer.get('bounded_search_status'), flush=True)

    # The crossing-free frontend case is recorded separately without assuming
    # that this optional exterior implementation supports it.
    diagram = Diagram.from_pd([])
    begin = time.perf_counter()
    answer = pachner_seed_decide(diagram, max_nodes=10, max_work=None)
    verified = None
    if answer['status'] == 'UNKNOT':
        verified = verify_transport_disk_certificate(diagram, answer['certificate'])
        if not verified:
            raise AssertionError('crossing-free proof rejected')
        accepted += 1
    elif answer['status'] != 'INCONCLUSIVE' or 'certificate' in answer:
        raise AssertionError('invalid crossing-free status')
    diagrams.append(dict(name='crossing_free_circle', pd=[],
        options=dict(max_nodes=10, max_work=None), result=answer,
        positive_replay=verified, elapsed_seconds=time.perf_counter()-begin))
    print('crossing_free_circle', answer['status'], flush=True)
    return dict(schema='pachner-region-integration-audit-v1',
        created_utc=datetime.now(timezone.utc).isoformat(),
        python=platform.python_version(), command=[sys.executable, *sys.argv],
        elapsed_seconds=time.perf_counter()-started, source_sha256=_source_inventory(),
        scope='small exact integration audit; no general speed or recognition-completeness claim',
        region_cases=records, diagram_cases=diagrams,
        summary=dict(region_cases=len(records), brute_region_calls=brute_calls,
            accepted_endpoint_replays=certificate_replays, diagram_cases=len(diagrams),
            positive_diagram_replays=accepted, rejected_wrong_diagram_proofs=rejected_sources,
            region_mismatches=0))


def replay(path):
    data = json.loads(Path(path).read_text())
    endpoint_count, diagram_count = 0, 0
    for case in data['region_cases']:
        proofs = case['wrapped']['endpoints'] + [proof for query in case['brute']
                                               for proof in query['result']['endpoints']]
        for proof in proofs:
            if not verify_pachner_endpoint(case['triangulation'], case['heights'], proof):
                raise AssertionError('retained endpoint proof rejected')
            endpoint_count += 1
    for case in data['diagram_cases']:
        answer = case['result']
        if 'certificate' in answer:
            if (answer['status'] != 'UNKNOT' or not verify_transport_disk_certificate(
                    Diagram.from_pd(case['pd']), answer['certificate'])):
                raise AssertionError('retained diagram proof rejected')
            diagram_count += 1
    return dict(endpoint_replays=endpoint_count, diagram_replays=diagram_count,
                input=str(path))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output')
    parser.add_argument('--replay')
    args = parser.parse_args()
    if not args.output and not args.replay:
        parser.error('supply --output for an audit or --replay for saved proof replay')
    result = replay(args.replay) if args.replay else run_audit()
    if args.output:
        target = Path(args.output)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(result, indent=2)+'\n')
        print('saved', target, flush=True)
    else:
        print(json.dumps(result))


if __name__ == '__main__':
    main()
