"""Independent saved whole-call replay and complete evidence accounting.

No discovery, historical pin reinterpretation or h transport occurs here.
LP/search counters are retained diagnostic bounds; accepted operations and
macro elementary counts are independently reconstructed from checked packets.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
from statistics import median

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import verify_crushing_recognition
from fastunknot.normal_pachner_descent_verify import verify_normal_pachner_descent
from fastunknot.normal_geometric_descent_verify import verify_normal_geometric_descent
from fastunknot.normal_surface_geometry import _prepare
from .common import (ARMS, BENCHMARK_PROTOCOL, CAP_STATS, MAX_STATS,
                     canonical_bytes, cases, configs, digest, same as _same, source_hashes)

if not __debug__:
    raise RuntimeError('research evidence replay requires assertions enabled')


def _endpoint_summary(source):
    if source is None:
        return dict(terminal=True, source_sha256=None, tetrahedra=None,
                    vertices=None, boundary_faces=None)
    prepared = _prepare(source, lambda: None)
    return dict(terminal=False, source_sha256=digest(source),
        tetrahedra=len(source['tetrahedra']), vertices=prepared['vertices'],
        boundary_faces=len(prepared['boundary_faces']))


def _macro(source, packet, method):
    """Fresh source-bound replay and direct D/UDD operation accounting."""
    assert packet['source_sha256'] == digest(source)
    if method == 'geometric':
        assert packet['schema'] == 'normal-geometric-descent-v1'
        assert verify_normal_geometric_descent(source, packet)
        steps = packet['steps']
        kinds = [step['certificate']['schema'] for step in steps]
    else:
        assert method == 'cochain' and packet['schema'] == 'normal-pachner-descent-v1'
        assert verify_normal_pachner_descent(source, packet)
        steps = packet['certificate']['moves']
        kinds = [step['transport']['move']['schema'] for step in steps]
    assert kinds in (['pachner-32-v1'], ['pachner-23-v1', 'pachner-32-v1', 'pachner-32-v1'])
    n = len(source['tetrahedra'])
    sizes = [len(step['triangulation']['tetrahedra']) for step in steps]
    assert sizes == ([n-1] if len(steps) == 1 else [n+1, n, n-1])
    assert _same(packet['successor'], steps[-1]['triangulation']) and n > 1
    return dict(schema=packet['schema'], source_sha256=digest(source),
        successor_sha256=digest(packet['successor']), initial_tetrahedra=n,
        intermediate_tetrahedra=sizes, word='D' if len(steps) == 1 else 'UDD',
        upward_moves=int(len(steps) == 3), downward_moves=1+int(len(steps) == 3),
        independently_replayed=True)

def _statistics(stats, options):
    assert type(stats) is dict
    assert all(type(k) is str and type(v) is int and v >= 0 for k, v in stats.items())
    assert all(k in MAX_STATS for k in stats if k.startswith(('maximum_', 'peak_', 'max_')))
    enabled = options.get('reduce_pachner_descent', False)
    for cap, fields in CAP_STATS.items():
        required = [f for f in fields if f != 'pachner_descent_macros' or enabled]
        assert all(f in stats for f in required)
        limit = options[cap]
        assert limit is None or type(limit) is int and limit >= 0
        assert limit is None or sum(stats.get(f, 0) for f in fields) <= limit
    assert {'pachner32_calls', 'pachner32_candidates', 'pachner32_moves'} <= stats.keys()
    assert stats['pachner32_moves'] <= stats['pachner32_calls'] <= stats['stages']
    assert stats['pachner32_candidates'] >= stats['pachner32_moves']
    fields = {'pachner_descent_calls', 'pachner_descent_nodes', 'pachner_descent_work',
              'pachner_descent_macros', 'pachner_descent_upward_moves', 'pachner_descent_downward_moves'}
    supplied = {k for k in stats if k.startswith('pachner_descent_')}
    if enabled:
        assert supplied == fields
        assert stats['pachner_descent_macros'] <= stats['pachner_descent_calls'] <= stats['stages']
        assert stats['pachner_descent_upward_moves'] <= stats['pachner_descent_macros']
        assert stats['pachner_descent_downward_moves'] == stats['pachner_descent_macros']+stats['pachner_descent_upward_moves']
    else:
        assert not supplied


def _driver_replay(diagram, result, options):
    """Native proof replay; caller binds the exact fresh experiment config."""
    diagram = Diagram.from_pd(diagram.pd)
    assert type(result) is dict and type(result['status']) is str
    assert result['status'] in ('UNKNOT', 'KNOTTED', 'INCONCLUSIVE')
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
        assert packet['status'] == result['status'] and verify_crushing_recognition(diagram, packet)
        chain = packet['chain']
    assert chain['schema'] == ('diagram-crushing-v5' if options['pachner_descent_method'] == 'geometric' else 'diagram-crushing-v4')
    initial = chain['source_triangulation']
    shelled = initial if chain['shelling'] is None else chain['shelling']['triangulation']
    assert stats['initial_tetrahedra'] == len(initial['tetrahedra'])
    assert stats['shelled_tetrahedra'] == len(shelled['tetrahedra'])
    schemas = {'normal-ray-crushing-v1': 'crushing_steps',
               'normal-boundary-unlayer-v1': 'boundary_unlayerings',
               'normal-pachner-32-v1': 'pachner32_moves',
               ('normal-geometric-descent-v1' if options['pachner_descent_method'] == 'geometric'
                else 'normal-pachner-descent-v1'): 'pachner_descent_macros'}
    counts = {field: 0 for field in schemas.values()}
    up = down = 0
    current = shelled
    macros = []
    for index, step in enumerate(chain['steps']):
        assert step['schema'] in schemas
        counts[schemas[step['schema']]] += 1
        assert current is not None
        if step['schema'] in ('normal-pachner-descent-v1', 'normal-geometric-descent-v1'):
            macro = _macro(current, step, options['pachner_descent_method'])
            macros.append(dict(chain_index=index, **macro))
            up += macro['upward_moves']
            down += macro['downward_moves']
        current = step['successor']
    assert _same(current, chain['triangulation'])
    assert all(stats.get(field, 0) == count for field, count in counts.items())
    assert stats.get('pachner_descent_upward_moves', 0) == up
    assert stats.get('pachner_descent_downward_moves', 0) == down
    assert stats['vertex_reduction_crushes'] <= counts['crushing_steps']
    assert stats['stages'] == len(chain['steps'])+int(chain['triangulation'] is not None)
    return dict(status=result['status'], proof_verified=result['status'] != 'INCONCLUSIVE',
        partial_chain_verified=result['status'] == 'INCONCLUSIVE', returned_work_complete=True,
        **counts, elementary_macro_upward_moves=up, elementary_macro_downward_moves=down,
        macros=macros, endpoint=_endpoint_summary(chain['triangulation']),
        final_tetrahedra=None if chain['triangulation'] is None else len(chain['triangulation']['tetrahedra']))


def replay_result(diagram, arm, result, options):
    assert __debug__, 'research replay requires assertions enabled'
    assert arm in ARMS and _same(options, configs(arm))
    return _driver_replay(diagram, result, options)


def _chain(result):
    return result['partial_chain'] if result['status'] == 'INCONCLUSIVE' else result['certificate']['chain']



def compare_endpoints(arms):
    """Compare the two fresh labelled endpoints without presuming equality."""
    assert set(arms) == set(ARMS)
    endpoints = {arm: _chain(arms[arm]['result'])['triangulation'] for arm in ARMS}
    summaries = {arm: _endpoint_summary(endpoints[arm]) for arm in ARMS}
    statuses = [arms[arm]['result']['status'] for arm in ARMS]
    return dict(endpoints=summaries,
        exact_typed_equality=_same(endpoints['cochain'], endpoints['geometric']),
        both_nonterminal=all(endpoints[arm] is not None for arm in ARMS),
        common_completed_verdict=statuses[0] if statuses[0] == statuses[1] and
            statuses[0] in ('UNKNOT', 'KNOTTED') else None,
        h_transport_claimed=False)


def check_audit(audit):
    assert __debug__, 'research replay requires assertions enabled'
    pins = source_hashes()
    assert type(audit) is dict and set(audit) == {'schema', 'passed', 'source_sha256',
        'config', 'case_order', 'records', 'wall_limit_seconds', 'unreturned_calls',
        'failures', 'active_call', 'coverage'}
    assert audit['schema'] == 'geometric-descent-audit-v1' and audit['passed'] is True
    assert _same(audit['source_sha256'], pins)
    assert _same(audit['config'], {arm: configs(arm) for arm in ARMS})
    assert audit['wall_limit_seconds'] is None and audit['unreturned_calls'] == []
    assert audit['failures'] == [] and audit['active_call'] is None
    definitions = cases()
    assert _same(audit['case_order'], [c['id'] for c in definitions])
    assert type(audit['records']) is list and len(audit['records']) == 7
    for record, case in zip(audit['records'], definitions):
        assert type(record) is dict and set(record) == set(case) | {'input_pd_sha256', 'arms', 'endpoint_comparison'}
        assert all(_same(record[k], v) for k, v in case.items())
        assert record['input_pd_sha256'] == digest(case['input_pd'])
        assert set(record['arms']) == set(ARMS)
        for arm in ARMS:
            retained = record['arms'][arm]
            assert type(retained) is dict and set(retained) == {'result', 'replay'}
            summary = replay_result(Diagram.from_pd(case['input_pd']), arm, retained['result'], configs(arm))
            assert _same(retained['replay'], summary)
            assert summary['status'] in ('INCONCLUSIVE', 'UNKNOT' if case['id'] == 'circle' else 'KNOTTED')
        assert _same(record['endpoint_comparison'], compare_endpoints(record['arms']))
    assert _same(audit['coverage'], dict(ordinary_calls_expected=14, ordinary_calls_completed=14))
    assert source_hashes() == pins
    return True


def eligible_benchmark(audit):
    """All five fixed cases must qualify; never choose cases after timings."""
    indexed = {record['id']: record for record in audit['records']}
    for name in BENCHMARK_PROTOCOL['case_ids']:
        statuses = [indexed[name]['arms'][arm]['result']['status'] for arm in ARMS]
        assert statuses[0] == statuses[1] and statuses[0] in ('UNKNOT', 'KNOTTED'), (name, statuses)
    return True


def timing_summary(record):
    samples = list(record['warmups'].values())
    samples += [s for pair in record['paired'] for s in pair['samples'].values()]
    samples += record['aa']['samples']
    statuses = {sample['status'] for sample in samples}
    eligible = len(statuses) == 1 and statuses <= {'UNKNOT', 'KNOTTED'}
    ratios = [pair['samples']['cochain']['elapsed_ns']/pair['samples']['geometric']['elapsed_ns']
              for pair in record['paired']] if eligible else []
    return dict(eligible_common_complete_outcome=eligible,
        common_status=next(iter(statuses)) if eligible else None,
        paired_cochain_over_geometric=ratios,
        median_paired_cochain_over_geometric=median(ratios) if ratios else None,
        median_ns={arm: median([p['samples'][arm]['elapsed_ns'] for p in record['paired']]) for arm in ARMS},
        aa_ratio=record['aa']['samples'][0]['elapsed_ns']/record['aa']['samples'][1]['elapsed_ns'],
        outcome_scope='Same completed whole-diagram verdict.' if eligible else
            'Resource-bounded outcomes retained; no recognition speed ratio.')


def check_benchmark(benchmark, audit, audit_bytes):
    assert check_audit(audit) and eligible_benchmark(audit)
    pins = source_hashes()
    assert type(benchmark) is dict and set(benchmark) == {'schema', 'passed', 'source_sha256',
        'audit_sha256', 'protocol', 'config', 'python', 'platform', 'records',
        'calls_completed', 'unreturned_calls', 'failures', 'active_call'}
    assert benchmark['schema'] == 'geometric-descent-benchmark-v1' and benchmark['passed'] is True
    assert _same(benchmark['source_sha256'], pins)
    assert benchmark['audit_sha256'] == sha256(audit_bytes).hexdigest()
    assert _same(benchmark['protocol'], BENCHMARK_PROTOCOL)
    assert _same(benchmark['config'], {arm: configs(arm) for arm in ARMS})
    assert type(benchmark['python']) is str and benchmark['python']
    assert type(benchmark['platform']) is str and benchmark['platform']
    assert benchmark['unreturned_calls'] == [] and _same(benchmark['calls_completed'], 50)
    assert benchmark['failures'] == [] and benchmark['active_call'] is None
    assert type(benchmark['records']) is list
    assert [r['id'] for r in benchmark['records']] == BENCHMARK_PROTOCOL['case_ids']
    indexed = {r['id']: r for r in audit['records']}
    count = 0
    for case_index, record in enumerate(benchmark['records']):
        assert set(record) == {'id', 'input_pd_sha256', 'warmups', 'paired', 'aa', 'summary'}
        case = indexed[record['id']]
        assert record['input_pd_sha256'] == case['input_pd_sha256']
        assert set(record['warmups']) == set(ARMS)
        samples = [(arm, record['warmups'][arm]) for arm in ARMS]
        assert type(record['paired']) is list and len(record['paired']) == 3
        for round_index, pair in enumerate(record['paired']):
            assert set(pair) == {'round', 'order', 'samples'}
            assert _same(pair['round'], round_index)
            assert _same(pair['order'], list(ARMS if (case_index+round_index) % 2 == 0 else reversed(ARMS)))
            assert set(pair['samples']) == set(ARMS)
            samples.extend((arm, pair['samples'][arm]) for arm in ARMS)
        assert set(record['aa']) == {'arm', 'samples'}
        assert record['aa']['arm'] == 'cochain' and type(record['aa']['samples']) is list
        assert len(record['aa']['samples']) == 2
        samples.extend(('cochain', sample) for sample in record['aa']['samples'])
        for arm, sample in samples:
            assert type(sample) is dict and set(sample) == {'elapsed_ns', 'status',
                'result_sha256', 'serialized_bytes', 'result', 'replay'}
            assert type(sample['elapsed_ns']) is int and sample['elapsed_ns'] > 0
            assert type(sample['serialized_bytes']) is int and sample['serialized_bytes'] > 0
            assert _same(sample['result'], case['arms'][arm]['result'])
            assert _same(sample['replay'], case['arms'][arm]['replay'])
            assert sample['status'] == sample['result']['status']
            payload = canonical_bytes(sample['result'])
            assert sample['result_sha256'] == sha256(payload).hexdigest()
            assert sample['serialized_bytes'] == len(payload)
            count += 1
        assert _same(record['summary'], timing_summary(record))
    assert count == BENCHMARK_PROTOCOL['total_calls'] == 50
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
    summary = dict(passed=True, ordinary_calls=14, endpoint_comparisons=7,
        discovery_used=False, general_quasipolynomial=False, source_files=len(audit['source_sha256']),
        outcomes={arm: [r['arms'][arm]['result']['status'] for r in audit['records']] for arm in ARMS},
        equal_endpoints=[r['id'] for r in audit['records'] if r['endpoint_comparison']['exact_typed_equality']])
    if benchmark is not None:
        summary.update(benchmark_cases=5, timed_and_warmup_calls=50,
            eligible_cases=[r['id'] for r in benchmark['records'] if r['summary']['eligible_common_complete_outcome']])
    if args.output:
        from .common import save
        save(args.output, summary)
    print(json.dumps(summary, sort_keys=True))


if __name__ == '__main__':
    main()
