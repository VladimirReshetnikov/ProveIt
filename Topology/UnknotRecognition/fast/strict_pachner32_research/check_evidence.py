"""Solver-free replay of complete coverage, source proofs and saved timings.

Operation counters are checked as recorded bounds and against retained moves;
they are not independently reconstructed LP operation traces. Historical pins
describe historical runs. Fresh proof replay uses the current pinned verifiers.
"""
import argparse
import gzip
from hashlib import sha256
import json
from pathlib import Path
from statistics import median

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import verify_crushing_recognition
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.normal_pachner32_verify import verify_normal_pachner32
from fastunknot.normal_surface_geometry import _prepare, _EDGES
from fastunknot.pachner23_verify import verify_pachner_23
from fastunknot.pachner32_verify import verify_pachner_32
from .common import (ARMS, BENCHMARK_PROTOCOL, CAP_STATS, MAX_STATS, PACKAGE,
                     canonical_bytes, cases, configs, digest, source_hashes)


def _same(actual, expected):
    if type(actual) is not type(expected):
        return False
    if type(expected) is dict:
        return actual.keys() == expected.keys() and all(_same(actual[k], v) for k, v in expected.items())
    if type(expected) in (list, tuple):
        return len(actual) == len(expected) and all(_same(a, b) for a, b in zip(actual, expected))
    return actual == expected


def _statistics(stats, options):
    assert type(stats) is dict
    assert all(type(k) is str and type(v) is int and v >= 0 for k, v in stats.items())
    assert all(k in MAX_STATS for k in stats if k.startswith(('maximum_', 'peak_', 'max_')))
    for cap, fields in CAP_STATS.items():
        required = [f for f in fields if f != 'pachner32_moves' or options['reduce_pachner32']]
        assert all(f in stats for f in required)
        limit = options[cap]
        assert limit is None or type(limit) is int and limit >= 0
        assert limit is None or sum(stats.get(f, 0) for f in fields) <= limit
    move_stats = {'pachner32_calls', 'pachner32_candidates', 'pachner32_moves'}
    if options['reduce_pachner32']:
        assert move_stats <= stats.keys()
        assert stats['pachner32_moves'] <= stats['pachner32_calls'] <= stats['stages']
        assert stats['pachner32_candidates'] >= stats['pachner32_moves']
    else:
        assert not move_stats.intersection(stats)


def replay_result(diagram, arm, result, options):
    """Authenticate the original PD and every returned complete/partial step."""
    assert __debug__, 'research replay requires assertions enabled'
    assert arm in ARMS and _same(options, configs(arm))
    diagram = Diagram.from_pd(diagram.pd)
    assert type(result) is dict and result['status'] in ('UNKNOT', 'KNOTTED', 'INCONCLUSIVE')
    stats = result['stats']
    _statistics(stats, options)
    assert not any(k.startswith('factors_') for k in stats)
    if result['status'] == 'INCONCLUSIVE':
        assert set(result) == {'status', 'reason', 'stats', 'partial_chain'}
        assert type(result['reason']) is str and result['reason']
        chain = result['partial_chain']
        assert chain['status'] == 'REDUCED' and verify_crushing_chain(diagram, chain)
    else:
        assert set(result) == {'status', 'certificate', 'stats'}
        packet = result['certificate']
        assert packet['status'] == result['status']
        assert verify_crushing_recognition(diagram, packet)
        chain = packet['chain']
    assert chain['schema'] == ('diagram-crushing-v3' if options['reduce_pachner32'] else 'diagram-crushing-v2')
    initial = chain['source_triangulation']
    shelled = initial if chain['shelling'] is None else chain['shelling']['triangulation']
    assert stats['initial_tetrahedra'] == len(initial['tetrahedra'])
    assert stats['shelled_tetrahedra'] == len(shelled['tetrahedra'])
    schemas = {'normal-ray-crushing-v1': 'crushing_steps',
               'normal-boundary-unlayer-v1': 'boundary_unlayerings',
               'normal-pachner-32-v1': 'pachner32_moves'}
    counts = {field: 0 for field in schemas.values()}
    for step in chain['steps']:
        assert step['schema'] in schemas
        counts[schemas[step['schema']]] += 1
    for field, value in counts.items():
        assert stats.get(field, 0) == value
    assert stats['vertex_reduction_crushes'] <= counts['crushing_steps']
    assert stats['stages'] == len(chain['steps'])+int(chain['triangulation'] is not None)
    return dict(status=result['status'], proof_verified=result['status'] != 'INCONCLUSIVE',
        partial_chain_verified=result['status'] == 'INCONCLUSIVE', returned_work_complete=True,
        **counts, final_tetrahedra=None if chain['triangulation'] is None else len(chain['triangulation']['tetrahedra']))


def _archive_files():
    directory = PACKAGE/'data/generation'
    manifest = json.loads((directory/'manifest.json').read_bytes())
    assert manifest['schema'] == 'strict-pachner32-historical-archive-v1'
    result = {}
    for name, entry in manifest['files'].items():
        assert type(name) is str and Path(name).name == name
        assert set(entry) == {'original_filename', 'original_sha256', 'stored_sha256', 'compression'}
        stored = (directory/name).read_bytes()
        assert sha256(stored).hexdigest() == entry['stored_sha256']
        assert entry['compression'] in (None, 'gzip')
        raw = gzip.decompress(stored) if entry['compression'] == 'gzip' else stored
        assert sha256(raw).hexdigest() == entry['original_sha256']
        original = entry['original_filename']
        assert original not in result
        result[original] = raw
    return result


def _candidates(source):
    p = _prepare(source, lambda: None)
    classes = {}
    for local, root in enumerate(p['edge_roots']):
        classes.setdefault(root, []).append(local)
    boundary = {p['edge_roots'][6*t+i] for t, f in p['boundary_faces']
                for i, edge in enumerate(_EDGES) if f not in edge}
    result = []
    for root, local in classes.items():
        if root in boundary or len(local) != 3 or len({i//6 for i in local}) != 3:
            continue
        incidences = [[i//6, *_EDGES[i % 6]] for i in local]
        t, a, b = min(incidences)
        result.append(dict(tetrahedron=t, vertices=[a, b], edge_root=root, incidences=incidences))
    return p, sorted(result, key=lambda c: (c['tetrahedron'], c['vertices']))


def check_archive():
    """Fresh replay of retained historical inputs; no historical-pin freshness claim."""
    assert __debug__, 'research replay requires assertions enabled'
    files = _archive_files()
    scan, query, regina, tiny = [json.loads(files[name]) for name in
        ('scan.json', 'euler-queries.json', 'regina-check.json', 'selfattachment-controls.json')]
    assert scan['passed'] is True and query['passed'] is True and regina['passed'] is True
    assert query['unreturned_calls'] == [] and query['wall_limit_seconds'] is None
    scan_hash = sha256(files['scan.json']).hexdigest()
    assert query['scan_file_sha256'] == regina['scan_file_sha256'] == scan_hash
    expected = ['trefoil', 'figure_eight', 'TT']
    for data in (scan, query, regina):
        assert [r['id'] for r in data['records']] == expected
    definitions = {c['id']: c for c in cases()}
    records, moves = [], 0
    for old, request, oracle in zip(scan['records'], query['records'], regina['records']):
        assert _same(old['input_pd'], definitions[old['id']]['input_pd'])
        assert old['chain']['status'] == 'REDUCED'
        assert verify_crushing_chain(Diagram.from_pd(old['input_pd']), old['chain'])
        source = old['chain']['triangulation']
        assert _same(source, old['initial_source']) and digest(source) == old['initial_source_sha256']
        assert type(old['initial_tetrahedra']) is int and old['initial_tetrahedra'] == len(source['tetrahedra'])
        assert len(old['rounds']) == len(old['steps'])+1
        assert len(oracle['steps']) == len(old['steps'])
        trace = [len(source['tetrahedra'])]
        for stage, step, external in zip(old['rounds'], old['steps'], oracle['steps']):
            prepared, candidates = _candidates(source)
            assert _same(stage['eligible_candidates'], candidates)
            assert _same(stage['vertices'], 1) and _same(stage['tetrahedra'], len(source['tetrahedra']))
            assert _same(stage['boundary_faces'], [list(f) for f in prepared['boundary_faces']])
            assert stage['source_sha256'] == step['source_sha256'] == digest(source)
            assert candidates and _same(step['candidate'], candidates[0])
            assert _same(stage['attempts'], [dict(candidate=candidates[0], status='ACCEPTED')])
            assert step['independent_replay'] is True
            assert verify_pachner_32(source, step['successor'], step['certificate'])
            assert len(step['successor']['tetrahedra']) == len(source['tetrahedra'])-1
            assert _prepare(step['successor'], lambda: None)['vertices'] == 1
            assert _same(external['candidate'], step['candidate'])
            assert external['regina_accepted'] is True and external['isomorphic'] is True
            source = step['successor']
            assert digest(source) == step['successor_sha256']
            trace.append(len(source['tetrahedra']))
            moves += 1
        prepared, candidates = _candidates(source)
        last = old['rounds'][-1]
        assert _same(last['eligible_candidates'], candidates) and candidates == []
        assert last['attempts'] == [] and last['source_sha256'] == digest(source)
        assert _same(source, old['final_source']) and digest(source) == old['final_source_sha256']
        assert _same(old['tetrahedron_trace'], trace) and _same(old['final_tetrahedra'], trace[-1])
        assert old['terminal_scan_complete'] is True and _same(request['source'], source)
        assert request['source_sha256'] == digest(source) and _same(request['tetrahedra'], trace[-1])
        result = request['result']
        assert set(result) == {'status', 'certificate', 'resolving_set', 'stats'}
        assert result['status'] == 'NO_POSITIVE_EULER'
        packet = result['certificate']
        assert _same(packet['allowed_types'], [[t, q] for t in range(trace[-1]) for q in range(3)])
        assert verify_euler_branch_tree(source, packet)
        resolving = sorted({node['tetrahedron'] for node in packet['nodes'] if node['kind'] == 'split'})
        assert _same(result['resolving_set'], resolving)
        stats = result['stats']
        assert all(type(v) is int and v >= 0 for v in stats.values())
        caps = {'max_nodes': 'nodes_attempted', 'max_pivots': 'lp_pivots',
                'max_anchors': 'anchors_tested', 'max_hitting_subsets': 'hitting_subsets_tested',
                'max_ellipsoid_iterations': 'lp_ellipsoid_iterations', 'max_feasibility_calls': 'lp_feasibility_calls'}
        for cap, field in caps.items():
            limit = query['config'][cap]
            assert type(limit) is int and 0 <= stats[field] <= limit
        assert _same(request['replay'], dict(status='NO_POSITIVE_EULER', negative_full_root_verified=True,
            complete_proof_nodes=len(packet['nodes']), resolving_set=resolving))
        records.append(dict(id=old['id'], initial_source_sha256=old['initial_source_sha256'],
            final_source_sha256=digest(source), tetrahedron_trace=trace, moves=len(old['steps']),
            full_root_negative_verified=True, resolving_set=resolving, h_upper_bound=len(resolving),
            proof_nodes=len(packet['nodes'])))
    assert moves == 9 and [r['tetrahedron_trace'] for r in records] == [
        [10, 9, 8], [13, 12], [23, 22, 21, 20, 19, 18, 17]]
    assert tiny['passed'] is True
    assert verify_pachner_23(tiny['initial'], tiny['source'], tiny['expansion_certificate'])
    assert verify_normal_pachner32(tiny['source'], tiny['packet'])
    region = {r['tetrahedron']: r['vertices'] for r in tiny['packet']['certificate']['region']}
    facets = {(t, f) for t, labels in region.items() for f in range(4) if labels[f] in (3, 4)}
    assert len(tiny['source']['tetrahedra']) == len(region) == 3 and len(facets) == 6
    pairs, unpaired = set(), 0
    for t, f in facets:
        record = tiny['source']['tetrahedra'][t][f]
        if record is None:
            unpaired += 1
        else:
            target = (record['tetrahedron'], record['permutation'][f])
            assert target in facets
            pairs.add(tuple(sorted(((t, f), target))))
    assert unpaired == len(pairs) == 2
    assert _same(tiny['formal_boundary']['formal_boundary_selfattachment_pairs'], 2)
    assert _same(tiny['malformed_count'], len(tiny['malformed_controls']))
    assert len(tiny['malformed_controls']) == 29
    for control in tiny['malformed_controls']:
        assert control['rejected'] is True
        assert verify_normal_pachner32(control['source'], control['packet']) is False
    return dict(passed=True, initial_diagram_chains=3, legacy_moves=9,
        full_root_negative_queries=3, records=records, selfattached_region_pairs=2,
        malformed_controls_rejected=29, discovery_used=False,
        historical_regina_comparisons_retained=9, fresh_regina_used=False,
        historical_pins_scope='Generation-time metadata, not current-source pin assertions.',
        h_scope='Upper bounds on the exact terminal sources; no invariance under retriangulation.')


replay_archives = check_archive


def check_audit(audit):
    assert __debug__, 'research replay requires assertions enabled'
    pins = source_hashes()
    assert audit['schema'] == 'strict-pachner32-audit-v1' and audit['passed'] is True
    assert _same(audit['source_sha256'], pins)
    assert _same(audit['config'], {arm: configs(arm) for arm in ARMS})
    assert audit['wall_limit_seconds'] is None and audit['unreturned_calls'] == []
    definitions = cases()
    assert _same(audit['case_order'], [c['id'] for c in definitions])
    assert type(audit['records']) is list and len(audit['records']) == 4
    for record, case in zip(audit['records'], definitions):
        assert all(_same(record[k], v) for k, v in case.items())
        assert record['input_pd_sha256'] == digest(case['input_pd'])
        assert set(record['arms']) == set(ARMS)
        for arm in ARMS:
            retained = record['arms'][arm]
            assert type(retained) is dict and set(retained) == {'result', 'replay'}
            summary = replay_result(Diagram.from_pd(case['input_pd']), arm, retained['result'], configs(arm))
            assert _same(retained['replay'], summary)
            assert summary['status'] in ('INCONCLUSIVE', 'UNKNOT' if case['id'] == 'circle' else 'KNOTTED')
    assert _same(audit['coverage'], dict(ordinary_calls_expected=8, ordinary_calls_completed=8))
    assert _same(audit['archival_replay'], check_archive())
    assert source_hashes() == pins
    return True


def check_benchmark(benchmark, audit, audit_bytes):
    assert check_audit(audit)
    pins = source_hashes()
    assert benchmark['schema'] == 'strict-pachner32-benchmark-v1' and benchmark['passed'] is True
    assert _same(benchmark['source_sha256'], pins)
    assert benchmark['audit_sha256'] == sha256(audit_bytes).hexdigest()
    assert _same(benchmark['protocol'], BENCHMARK_PROTOCOL)
    assert _same(benchmark['config'], {arm: configs(arm) for arm in ARMS})
    assert benchmark['unreturned_calls'] == [] and _same(benchmark['calls_completed'], 30)
    assert [r['id'] for r in benchmark['records']] == BENCHMARK_PROTOCOL['case_ids']
    indexed = {r['id']: r for r in audit['records']}
    count = 0
    for case_index, record in enumerate(benchmark['records']):
        case = indexed[record['id']]
        assert record['input_pd_sha256'] == case['input_pd_sha256']
        assert set(record['warmups']) == set(ARMS)
        reference, all_samples = {}, []
        for arm in ARMS:
            warmup = record['warmups'][arm]
            assert _same(warmup['result'], case['arms'][arm]['result'])
            assert _same(warmup['replay'], case['arms'][arm]['replay'])
            payload = canonical_bytes(warmup['result'])
            reference[arm] = dict(status=warmup['result']['status'],
                result_sha256=sha256(payload).hexdigest(), serialized_bytes=len(payload))
            all_samples.append((arm, warmup, True))
        assert len(record['paired']) == 3
        for round_index, pair in enumerate(record['paired']):
            assert _same(pair['round'], round_index)
            assert pair['order'] == list(ARMS if (case_index+round_index) % 2 == 0 else reversed(ARMS))
            assert set(pair['samples']) == set(ARMS)
            all_samples.extend((arm, pair['samples'][arm], False) for arm in ARMS)
        assert record['aa']['arm'] == 'baseline' and len(record['aa']['samples']) == 2
        all_samples.extend(('baseline', sample, False) for sample in record['aa']['samples'])
        for arm, sample, warmup in all_samples:
            fields = {'elapsed_ns', 'status', 'result_sha256', 'serialized_bytes'}
            assert type(sample) is dict and set(sample) == fields | ({'result', 'replay'} if warmup else set())
            assert type(sample['elapsed_ns']) is int and sample['elapsed_ns'] > 0
            assert type(sample['serialized_bytes']) is int and sample['serialized_bytes'] > 0
            assert all(_same(sample[k], v) for k, v in reference[arm].items())
            count += 1
        statuses = {sample['status'] for _, sample, _ in all_samples}
        eligible = len(statuses) == 1 and statuses <= {'UNKNOT', 'KNOTTED'}
        ratios = [pair['samples']['baseline']['elapsed_ns']/pair['samples']['pachner32']['elapsed_ns']
                  for pair in record['paired']] if eligible else []
        summary = dict(eligible_common_complete_outcome=eligible,
            common_status=next(iter(statuses)) if eligible else None,
            paired_baseline_over_pachner32=ratios,
            median_paired_baseline_over_pachner32=median(ratios) if ratios else None,
            median_ns={arm: median([p['samples'][arm]['elapsed_ns'] for p in record['paired']]) for arm in ARMS},
            aa_ratio=record['aa']['samples'][0]['elapsed_ns']/record['aa']['samples'][1]['elapsed_ns'],
            outcome_scope='Same completed whole-diagram verdict.' if eligible else
                'Resource-bounded outcomes retained; no recognition speed ratio.')
        assert _same(record['summary'], summary)
    assert count == BENCHMARK_PROTOCOL['total_calls'] == 30
    assert source_hashes() == pins
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', type=Path, required=True)
    parser.add_argument('--benchmark', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    raw = args.audit.read_bytes()
    audit = json.loads(raw)
    benchmark = json.loads(args.benchmark.read_bytes()) if args.benchmark else None
    assert check_audit(audit) if benchmark is None else check_benchmark(benchmark, audit, raw)
    summary = dict(passed=True, ordinary_calls=8, discovery_used=False,
        general_quasipolynomial=False, source_files=len(audit['source_sha256']),
        archival_initial_chains=3, archival_moves=9, archival_negative_queries=3,
        outcomes={arm: [r['arms'][arm]['result']['status'] for r in audit['records']] for arm in ARMS})
    if benchmark is not None:
        summary.update(benchmark_cases=3, timed_and_warmup_calls=30,
            eligible_cases=[r['id'] for r in benchmark['records'] if r['summary']['eligible_common_complete_outcome']])
    if args.output:
        args.output.write_bytes(canonical_bytes(summary)+b'\n')
    print(json.dumps(summary, sort_keys=True))


if __name__ == '__main__':
    main()
