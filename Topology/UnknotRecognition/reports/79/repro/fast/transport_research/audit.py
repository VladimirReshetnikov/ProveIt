"""Audit local scores, native transport, move paths, and source-diagram descent.

Run with a PYTHONPATH containing fast/ and optional Regina.  All positive
surface counts use native component certificates.  No Euler-only verdicts
or complete-unknot coverage claims are emitted.
"""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import platform
import random
from statistics import median
import time

from fastunknot import Diagram
from fastunknot.cocycle_transport import (
    bipyramid_cocycle_score, cocycle_collapse_candidates, descend_cocycle,
    transport_cocycle, _collapse_region,
)
from fastunknot.cocycle_transport_verify import verify_cocycle_transport
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import (
    rank_one_cocycle_seed, _rank_one_cocycle_seed_details, _height_summary,
    _Budget, CocycleLimit,
)
from fastunknot.normal_disk_kernel import (
    normal_compressing_disk_count, verify_normal_disk_count_certificate,
)
from fastunknot.normal_surface_geometry import _prepare, _coordinates, _EDGES
from fastunknot.pachner23 import pachner_23
from fastunknot.pachner32 import pachner_32
from fastunknot.pachner32_verify import verify_pachner_32
from normal_orbit_research.fixtures import layered_torus

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT.parent/'synthesis/data'
BASELINE = '3a90fb34146c915328ab8eac6250cc2514f74ed0'


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def edge_magnitude(heights):
    return max(max(row)-min(row) for row in heights)


def independent_local_score(heights):
    c, d, e, a, b = heights
    span = lambda *x: max(x)-min(x)
    pieces = (span(a,b,c,d)+span(a,b,d,e)+span(a,b,e,c)
              -span(a,c,d,e)-span(b,c,d,e))
    arcs = span(a,b,c)+span(a,b,d)+span(a,b,e)-span(c,d,e)
    return abs(a-b)-arcs+pieces, pieces


def scalar_audit():
    profile = Counter()
    for heights in product(range(-2, 3), repeat=5):
        score = bipyramid_cocycle_score(heights)
        euler, pieces = independent_local_score(heights)
        assert (euler, pieces) == (-score['euler_loss'], score['normal_disc_increase'])
        assert pieces >= score['gap'] >= 0
        profile[euler, pieces] += 1
    return dict(cases=5**5, histogram=[dict(euler_jump=k[0], normal_disc_jump=k[1], cases=v)
                                      for k, v in sorted(profile.items())])


def random_paths(steps=30, regina=True):
    rng = random.Random(20261009917)
    fixtures = [('layered-2', layered_torus(2)[0]), ('layered-8', layered_torus(8)[0]),
                ('one-crossing', diagram_exterior(Diagram.from_braid(2, [1]))),
                ('trefoil', diagram_exterior(Diagram.from_braid(2, [1,1,1])))]
    if regina:
        from normal_orbit_research.fixtures import regina_triangulation, regina_surface
    records = []
    for name, initial in fixtures:
        raw = initial
        h = rank_one_cocycle_seed(raw)['heights']
        for step in range(steps):
            candidates = cocycle_collapse_candidates(raw, h)['candidates']
            use_down = bool(candidates) and (len(raw['tetrahedra']) > len(initial['tetrahedra'])+8
                                             or rng.randrange(2))
            if regina:
                reference = regina_triangulation(raw)
            if use_down:
                selected = rng.choice(candidates)
                t, vertices = selected['tetrahedron'], selected['vertices']
                replacement = pachner_32(raw, t, vertices)
                if regina:
                    site = reference.tetrahedron(t).edge(_EDGES.index(tuple(vertices)))
            else:
                sites = [(t,f) for t, row in enumerate(raw['tetrahedra']) for f, r in enumerate(row)
                         if r is not None and r['tetrahedron'] != t]
                t, f = rng.choice(sites)
                replacement = pachner_23(raw, t, f)
                if regina:
                    site = reference.tetrahedron(t).triangle(f)
            after = replacement['triangulation']
            result = transport_cocycle(raw, h, after, replacement['certificate'])
            assert verify_cocycle_transport(raw, h, after, result['certificate'])
            old_size, new_size = edge_magnitude(h), edge_magnitude(result['heights'])
            assert new_size <= old_size if use_down else new_size <= 2*old_size
            record = dict(fixture=name, step=step, direction='3-2' if use_down else '2-3',
                tetrahedra=len(after['tetrahedra']), edge_magnitude_before=old_size,
                edge_magnitude_after=new_size, score=result['score'],
                euler_jump=result['certificate']['euler_jump'],
                normal_disc_jump=result['certificate']['normal_disc_jump'],
                certificate_sha256=digest(result['certificate']))
            if regina:
                assert reference.pachner(site)
                imported = regina_triangulation(after)
                assert reference.isoSig() == imported.isoSig()
                surface = regina_surface(imported, result['coordinates'])
                analysed = _coordinates(_prepare(after, lambda: None), result['coordinates'], lambda: None)
                assert int(str(surface.eulerChar())) == analysed['euler_characteristic']
                record['regina'] = dict(euler=int(str(surface.eulerChar())),
                                       connected=surface.isConnected(), orientable=surface.isOrientable())
            records.append(record)
            raw, h = after, result['heights']
    return records


def obstruction_audit():
    source = json.loads((DATA/'coherent-obstruction-certificate.json').read_text())
    raw = source['moves'][-1]['triangulation']
    seed = rank_one_cocycle_seed(raw)
    result = descend_cocycle(raw, seed['heights'])
    disk = normal_compressing_disk_count(result['triangulation'], result['coordinates'], record_certificate=True)
    assert disk['compressing_disk_components'] == 1
    assert verify_normal_disk_count_certificate(result['triangulation'], result['coordinates'], disk['certificate'])
    return dict(source_triangulation=raw, source_heights=seed['heights'],
                descent=result, disk_certificate=disk['certificate'])


def restart_descent(raw, heights, check):
    """Experimental old policy: first site, then a new maximal-tree gauge."""
    moves = []
    while True:
        check()
        candidates = cocycle_collapse_candidates(raw, heights, check=check)['candidates']
        if not candidates:
            break
        c = candidates[0]
        replacement = pachner_32(raw, c['tetrahedron'], c['vertices'], check=check)
        after = replacement['triangulation']
        assert verify_pachner_32(raw, after, replacement['certificate'], check=check)
        seed = rank_one_cocycle_seed(after, check=check)
        moves.append(dict(triangulation=after, move=replacement['certificate']))
        raw, heights = after, seed['heights']
    from fastunknot.normal_cocycle import local_coordinates
    return dict(triangulation=raw, heights=heights, coordinates=[local_coordinates(row) for row in heights],
                moves=moves, stats=dict(moves=len(moves), remaining_tetrahedra=len(raw['tetrahedra'])))


def corpus_audit(corpus, max_crossings=16, max_work=2000000, max_cycles=5000):
    records, proofs = [], {}
    entries = json.loads(Path(corpus).read_text())['source_cases']
    for entry in entries:
        source = entry['source']
        if len(source['pd']) > max_crossings:
            continue
        diagram = Diagram.from_pd(source['pd'])
        raw = diagram_exterior(diagram)
        seed, prepared = _rank_one_cocycle_seed_details(raw)
        initial = _height_summary(prepared, seed['heights'])
        record = dict(source=source, initial=initial, initial_tetrahedra=len(raw['tetrahedra']),
                      initial_edge_magnitude=edge_magnitude(seed['heights']), arms={})
        for strategy in ('first-regauge', 'first-transport', 'score-transport'):
            budget = _Budget(lambda: None, max_work)
            start = time.perf_counter()
            phase = 'descent'
            try:
                if strategy == 'first-regauge':
                    descent = restart_descent(raw, seed['heights'], budget.tick)
                else:
                    descent = descend_cocycle(raw, seed['heights'], strategy=strategy.split('-')[0],
                                             check=budget.tick)
                phase = 'disk-components'
                disk = normal_compressing_disk_count(descent['triangulation'], descent['coordinates'],
                    max_cycles=max_cycles, check=budget.tick, record_certificate=True)
                analysed = _coordinates(_prepare(descent['triangulation'], budget.tick),
                                        descent['coordinates'], budget.tick)
                answer = dict(status=disk['status'], stats=descent['stats'],
                    euler=analysed['euler_characteristic'], normal_disks=analysed['normal_disks'],
                    edge_magnitude=edge_magnitude(descent['heights']), orbit_stats=disk['stats'])
                if disk['status'] == 'COMPLETE':
                    phase = 'independent-disk-replay'
                    assert verify_normal_disk_count_certificate(descent['triangulation'],
                        descent['coordinates'], disk['certificate'], check=budget.tick)
                    answer['compressing_disks'] = disk['compressing_disk_components']
                    if disk['compressing_disk_components']:
                        assert source['expected'] == 'UNKNOT'
                        if strategy == 'first-regauge':
                            proof = dict(schema='diagram-regauge-research-v1',
                                input_pd=source['pd'], source_triangulation=raw,
                                moves=descent['moves'], coordinates=descent['coordinates'],
                                disk_certificate=disk['certificate'])
                        else:
                            from fastunknot.normal_transport_verify import verify_transport_disk_certificate
                            proof = dict(schema='diagram-transport-disc-v1', input_pd=source['pd'],
                                source_triangulation=raw, shelling=None,
                                source_heights=seed['heights'], steps=descent['moves'],
                                coordinates=descent['coordinates'], disc_certificate=disk['certificate'])
                            phase = 'independent-source-replay'
                            assert verify_transport_disk_certificate(diagram, proof, check=budget.tick)
                            answer['source_certificate_verified'] = True
                        key = digest(proof)
                        proofs[key] = proof
                        answer['proof_sha256'] = key
            except CocycleLimit:
                answer = dict(status='WORK_LIMIT', phase=phase)
            answer.update(work=budget.work, seconds=time.perf_counter()-start)
            record['arms'][strategy] = answer
        records.append(record)
        print(source['name'], [(k,v['status'],v.get('compressing_disks'),v.get('euler'))
                              for k,v in record['arms'].items()], flush=True)
    return dict(records=records, proofs=proofs)


def independent_expansions(n):
    """Expand floor(n/2) disjoint tetrahedron pairs of a layered solid torus."""
    raw, _ = layered_torus(n)
    h = rank_one_cocycle_seed(raw)['heights']
    for t in reversed(range(0, n-1, 2)):
        replacement = pachner_23(raw, t, 0)
        result = transport_cocycle(raw, h, replacement['triangulation'], replacement['certificate'])
        raw, h = replacement['triangulation'], result['heights']
    return raw, h


def score_benchmark(sizes, rounds=3):
    records = []
    for n in sizes:
        raw, h = independent_expansions(n)
        prepared = _prepare(raw, lambda: None)
        assert prepared['vertices'] == 1
        initial = _height_summary(prepared, h)
        def local():
            candidates = cocycle_collapse_candidates(raw, h)['candidates']
            return [(c['tetrahedron'], c['vertices'], initial['euler_characteristic']+c['euler_gain'],
                     initial['normal_pieces']-c['normal_disc_saving']) for c in candidates]
        def restart():
            # Recognize the same sites without computing any local score.
            # The baseline reconstructs a fresh primitive H1 representative
            # after every candidate move. One global vertex makes the normal
            # vector independent of the seed's possible orientation reversal.
            p = _prepare(raw, lambda: None)
            groups = {}
            for local, root in enumerate(p['edge_roots']):
                groups.setdefault(root, []).append((local//6, *_EDGES[local%6]))
            sites = []
            for occurrences in groups.values():
                if _collapse_region(p['tetrahedra'], occurrences, lambda: None) is not None:
                    t, a, b = occurrences[0]
                    sites.append(dict(tetrahedron=t, vertices=[a,b]))
            result = []
            for c in sites:
                after = pachner_32(raw, c['tetrahedron'], c['vertices'])['triangulation']
                seed, p = _rank_one_cocycle_seed_details(after)
                summary = _height_summary(p, seed['heights'])
                result.append((c['tetrahedron'], c['vertices'], summary['euler_characteristic'],
                               summary['normal_pieces']))
            return result
        expected = local()
        assert restart() == expected
        timing = {'local': [], 'restart': []}
        for trial in range(rounds):
            arms = [('local', local), ('restart', restart)]
            if trial % 2:
                arms.reverse()
            for name, function in arms:
                start = time.perf_counter()
                answer = function()
                elapsed = time.perf_counter()-start
                assert answer == expected
                timing[name].append(elapsed)
        record = dict(original_tetrahedra=n, tetrahedra=len(raw['tetrahedra']),
            candidates=len(expected), height_bits=edge_magnitude(h).bit_length(),
            seconds=timing, median_seconds={k:median(v) for k,v in timing.items()})
        record['median_speedup'] = record['median_seconds']['restart']/record['median_seconds']['local']
        records.append(record)
        print('benchmark', n, len(expected), record['median_seconds'], flush=True)
    return records


def source_pins():
    paths = [Path(__file__), ROOT/'fastunknot/cocycle_transport.py',
             ROOT/'fastunknot/cocycle_transport_verify.py', ROOT/'tests/test_cocycle_transport.py']
    return {str(path.relative_to(ROOT.parent)): sha256(path.read_bytes()).hexdigest() for path in paths}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('local', 'corpus', 'benchmark'))
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--corpus', type=Path, default=DATA/'cocycle-reuse-audit.json')
    parser.add_argument('--max-crossings', type=int, default=16)
    parser.add_argument('--steps', type=int, default=30)
    parser.add_argument('--rounds', type=int, default=3)
    parser.add_argument('--sizes', type=int, nargs='+', default=[16,32,64,128])
    parser.add_argument('--no-regina', action='store_true')
    args = parser.parse_args()
    start = time.perf_counter()
    if args.mode == 'local':
        result = dict(scalar=scalar_audit(), moves=random_paths(args.steps, not args.no_regina),
                      obstruction=obstruction_audit())
    elif args.mode == 'corpus':
        result = corpus_audit(args.corpus, args.max_crossings)
    else:
        result = dict(benchmarks=score_benchmark(args.sizes, args.rounds))
    result.update(mode=args.mode, baseline_commit=BASELINE, python=platform.python_version(),
                  elapsed_seconds=time.perf_counter()-start, source_sha256=source_pins())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('completed', args.mode, result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
