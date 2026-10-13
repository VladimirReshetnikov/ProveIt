"""Independent saved proof, coverage, work-accounting and timing replay.

No factor producer, recognition producer, LP solver, or discovery runner is
imported. Partial results authenticate only their retained smaller exteriors.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
from statistics import median

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import verify_crushing_recognition
from fastunknot.factored_crushing_verify import (
    _factor_diagrams, _pd_equal, verify_factored_crushing_recognition)
from .common import (ARMS, BENCHMARK_PROTOCOL, CAP_STATS, MAX_STATS, canonical_bytes,
                     cases, configs, digest, repeated_trefoils, source_hashes)

FACTOR_STATS = frozenset(('factors_total', 'factors_attempted', 'factors_unknot',
                          'factors_knotted', 'factors_inconclusive'))


def _same(actual, expected):
    """Exact JSON-like equality, without bool/int or float/int conflation."""
    if type(actual) is not type(expected):
        return False
    if type(expected) is dict:
        return (actual.keys() == expected.keys() and
                all(_same(actual[k], v) for k, v in expected.items()))
    if type(expected) in (list, tuple):
        return len(actual) == len(expected) and all(_same(a, b) for a, b in zip(actual, expected))
    return actual == expected


def _statistics(stats, options):
    assert type(stats) is dict
    assert all(type(k) is str and type(v) is int and v >= 0 for k, v in stats.items())
    for key in stats:
        if key.startswith(('maximum_', 'peak_', 'max_')):
            assert key in MAX_STATS, 'unknown peak-statistic accounting contract'
    for cap, fields in CAP_STATS.items():
        assert cap in options and all(field in stats for field in fields)
        limit = options[cap]
        assert limit is None or type(limit) is int and limit >= 0
        assert limit is None or sum(stats[field] for field in fields) <= limit


def _raw(diagram, result, options):
    assert type(result) is dict and result['status'] in ('UNKNOT', 'KNOTTED', 'INCONCLUSIVE')
    stats = result['stats']
    _statistics(stats, options)
    assert not FACTOR_STATS.intersection(stats)
    if result['status'] == 'INCONCLUSIVE':
        assert set(result) == {'status', 'reason', 'stats', 'partial_chain'}
        assert type(result['reason']) is str and result['reason']
        chain = result['partial_chain']
        assert verify_crushing_chain(diagram, chain) and chain['status'] == 'REDUCED'
    else:
        assert set(result) == {'status', 'certificate', 'stats'}
        packet = result['certificate']
        assert packet['status'] == result['status']
        assert verify_crushing_recognition(diagram, packet)
        chain = packet['chain']
    assert chain['schema'] == ('diagram-crushing-v2' if options['unlayer_boundary'] else 'diagram-crushing-v1')
    initial = chain['source_triangulation']
    shelled = initial if chain['shelling'] is None else chain['shelling']['triangulation']
    assert stats['initial_tetrahedra'] == len(initial['tetrahedra'])
    assert stats['shelled_tetrahedra'] == len(shelled['tetrahedra'])
    unlayers = sum(packet['schema'] == 'normal-boundary-unlayer-v1' for packet in chain['steps'])
    crushes = len(chain['steps'])-unlayers
    assert stats['crushing_steps'] == crushes and stats['boundary_unlayerings'] == unlayers
    assert stats.get('vertex_reduction_crushes', 0) <= crushes
    return dict(status=result['status'], proof_verified=result['status'] != 'INCONCLUSIVE',
        partial_chain_verified=result['status'] == 'INCONCLUSIVE', returned_work_complete=True,
        crushing_steps=crushes, boundary_unlayerings=unlayers,
        final_tetrahedra=None if chain['triangulation'] is None else len(chain['triangulation']['tetrahedra']))


def replay_result(diagram, arm, result, config):
    """Replay every returned child and independently recompute shared totals."""
    assert __debug__, 'research replay requires assertions enabled'
    assert _same(config, configs())
    diagram = Diagram.from_pd(diagram.pd)
    assert arm in ARMS
    if arm == 'raw':
        return _raw(diagram, result, config)

    assert type(result) is dict
    status = result['status']
    assert status in ('UNKNOT', 'KNOTTED', 'INCONCLUSIVE')
    common = {'status', 'stats', 'factor_results', 'factorization', 'factor_pds'}
    assert set(result) == common | ({'reason'} if status == 'INCONCLUSIVE' else {'certificate'})
    if status == 'INCONCLUSIVE':
        assert type(result['reason']) is str and result['reason']
    factors = _factor_diagrams(diagram, result['factorization'], lambda: None)
    assert type(result['factor_pds']) is list and len(result['factor_pds']) == len(factors)
    for pd, factor in zip(result['factor_pds'], factors):
        assert _pd_equal(pd, factor.pd, lambda: None)
    attempts = result['factor_results']
    assert type(attempts) is list and 1 <= len(attempts) <= len(factors)
    order = sorted(range(len(factors)), key=lambda i: (factors[i].crossings, i))
    stats = dict(factors_total=len(factors), factors_attempted=0,
                 factors_unknot=0, factors_knotted=0, factors_inconclusive=0)
    for fields in CAP_STATS.values():
        for field in fields:
            stats[field] = 0
    children, proofs = [], {}
    for position, attempt in enumerate(attempts):
        assert type(attempt) is dict and set(attempt) == {'factor_index', 'result'}
        index = attempt['factor_index']
        assert type(index) is int and index == order[position]
        local = dict(config)
        for cap, fields in CAP_STATS.items():
            if config[cap] is not None:
                used = sum(stats[field] for field in fields)
                assert used <= config[cap]
                local[cap] = config[cap]-used
        child = attempt['result']
        children.append(dict(factor_index=index, **_raw(factors[index], child, local)))
        for key, value in child['stats'].items():
            stats[key] = max(stats.get(key, 0), value) if key in MAX_STATS else stats.get(key, 0)+value
        stats['factors_attempted'] += 1
        stats['factors_'+child['status'].lower()] += 1
        if child['status'] != 'INCONCLUSIVE':
            proofs[index] = child['certificate']
        if child['status'] == 'KNOTTED':
            assert position == len(attempts)-1 and status == 'KNOTTED'
    _statistics(result['stats'], config)
    assert _same(result['stats'], stats), 'incorrect additive or peak factor totals'
    if status == 'UNKNOT':
        assert len(attempts) == len(factors) and stats['factors_unknot'] == len(factors)
        expected_proofs = [dict(factor_index=i, certificate=proofs[i]) for i in range(len(factors))]
    elif status == 'KNOTTED':
        assert stats['factors_knotted'] == 1
        index = attempts[-1]['factor_index']
        expected_proofs = [dict(factor_index=index, certificate=proofs[index])]
    else:
        assert len(attempts) == len(factors) and stats['factors_inconclusive'] > 0
        assert stats['factors_knotted'] == 0
    if status != 'INCONCLUSIVE':
        packet = result['certificate']
        assert _same(packet['factorization'], result['factorization'])
        assert _same(packet['factor_pds'], result['factor_pds'])
        assert _same(packet['proofs'], expected_proofs) and packet['status'] == status
        assert verify_factored_crushing_recognition(diagram, packet)
    return dict(status=status, proof_verified=status != 'INCONCLUSIVE',
        partial_chain_verified=status == 'INCONCLUSIVE', returned_work_complete=True,
        factors_total=len(factors), factors_attempted=len(attempts),
        attempted_indices=[a['factor_index'] for a in attempts], children=children,
        crushing_steps=stats['crushing_steps'], boundary_unlayerings=stats['boundary_unlayerings'])


def check_audit(audit):
    """Require every predeclared ordinary call, plus exactly requested scaling."""
    assert __debug__, 'research replay requires assertions enabled'
    pins = source_hashes()
    assert audit['schema'] == 'factored-crushing-audit-v1' and audit['passed'] is True
    assert _same(audit['source_sha256'], pins) and _same(audit['config'], configs())
    assert audit['wall_limit_seconds'] is None and audit['unreturned_calls'] == []
    definitions = cases()
    assert _same(audit['case_order'], [c['id'] for c in definitions])
    assert type(audit['records']) is list and len(audit['records']) == len(definitions)
    for record, case in zip(audit['records'], definitions):
        for key, value in case.items():
            assert _same(record[key], value)
        assert record['input_pd_sha256'] == digest(case['input_pd'])
        diagram = Diagram.from_pd(case['input_pd'])
        assert set(record['arms']) == set(ARMS)
        for arm in ARMS:
            retained = record['arms'][arm]
            assert type(retained) is dict and set(retained) == {'result', 'replay'}
            summary = replay_result(diagram, arm, retained['result'], audit['config'])
            assert _same(retained['replay'], summary)
            if summary['status'] != 'INCONCLUSIVE':
                assert summary['status'] == ('UNKNOT' if case['id'] in ('circle', 'UU') else 'KNOTTED')
    assert type(audit['scaling_requested']) is bool
    definitions = [repeated_trefoils(k) for k in (2, 4, 8, 16)] if audit['scaling_requested'] else []
    assert type(audit['scaling']) is list and len(audit['scaling']) == len(definitions)
    for record, case in zip(audit['scaling'], definitions):
        for key, value in case.items():
            assert _same(record[key], value)
        assert record['input_pd_sha256'] == digest(case['input_pd'])
        summary = replay_result(Diagram.from_pd(case['input_pd']), 'factored', record['result'], audit['config'])
        assert _same(record['replay'], summary)
        assert summary['status'] in ('KNOTTED', 'INCONCLUSIVE')
    assert _same(audit['coverage'], dict(ordinary_calls_expected=16, ordinary_calls_completed=16,
        scaling_calls_expected=len(definitions), scaling_calls_completed=len(definitions)))
    assert source_hashes() == pins
    return True


def check_benchmark(benchmark, audit, audit_bytes):
    assert check_audit(audit)
    pins = source_hashes()
    assert benchmark['schema'] == 'factored-crushing-benchmark-v1' and benchmark['passed'] is True
    assert _same(benchmark['source_sha256'], pins)
    assert benchmark['audit_sha256'] == sha256(audit_bytes).hexdigest()
    assert _same(benchmark['protocol'], BENCHMARK_PROTOCOL) and _same(benchmark['config'], configs())
    assert benchmark['unreturned_calls'] == []
    assert type(benchmark['calls_completed']) is int and benchmark['calls_completed'] == 50
    assert [r['id'] for r in benchmark['records']] == BENCHMARK_PROTOCOL['case_ids']
    indexed = {r['id']: r for r in audit['records']}
    count = 0
    for case_index, record in enumerate(benchmark['records']):
        case = indexed[record['id']]
        assert record['input_pd_sha256'] == case['input_pd_sha256']
        assert set(record['warmups']) == set(ARMS)
        reference = {}
        all_samples = []
        for arm in ARMS:
            warmup = record['warmups'][arm]
            assert _same(warmup['result'], case['arms'][arm]['result'])
            assert _same(warmup['replay'], case['arms'][arm]['replay'])
            payload = canonical_bytes(warmup['result'])
            reference[arm] = dict(status=warmup['result']['status'],
                result_sha256=sha256(payload).hexdigest(), serialized_bytes=len(payload))
            all_samples.append((arm, warmup, True))
        assert len(record['paired']) == BENCHMARK_PROTOCOL['paired_rounds']
        for round_index, pair in enumerate(record['paired']):
            assert type(pair['round']) is int and pair['round'] == round_index
            assert pair['order'] == list(ARMS if (case_index+round_index) % 2 == 0 else reversed(ARMS))
            assert set(pair['samples']) == set(ARMS)
            all_samples.extend((arm, pair['samples'][arm], False) for arm in ARMS)
        assert record['aa']['arm'] == 'raw' and len(record['aa']['samples']) == 2
        all_samples.extend(('raw', sample, False) for sample in record['aa']['samples'])
        for arm, sample, warmup in all_samples:
            fields = {'elapsed_ns', 'status', 'result_sha256', 'serialized_bytes'}
            assert type(sample) is dict and set(sample) == fields | ({'result', 'replay'} if warmup else set())
            assert type(sample['elapsed_ns']) is int and sample['elapsed_ns'] > 0
            assert type(sample['serialized_bytes']) is int and sample['serialized_bytes'] > 0
            assert all(_same(sample[key], value) for key, value in reference[arm].items())
            count += 1
        statuses = {sample['status'] for _, sample, _ in all_samples}
        eligible = len(statuses) == 1 and statuses <= {'UNKNOT', 'KNOTTED'}
        ratios = [pair['samples']['raw']['elapsed_ns']/pair['samples']['factored']['elapsed_ns']
                  for pair in record['paired']] if eligible else []
        summary = dict(eligible_common_complete_outcome=eligible,
            common_status=next(iter(statuses)) if eligible else None,
            paired_raw_over_factored=ratios,
            median_paired_raw_over_factored=median(ratios) if ratios else None,
            median_ns={arm: median([p['samples'][arm]['elapsed_ns'] for p in record['paired']]) for arm in ARMS},
            aa_ratio=record['aa']['samples'][0]['elapsed_ns']/record['aa']['samples'][1]['elapsed_ns'],
            outcome_scope='Same completed whole-diagram verdict.' if eligible else
                'Resource-bounded outcomes retained; no recognition speed ratio.')
        assert _same(record['summary'], summary)
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
    benchmark = None
    if args.benchmark:
        benchmark = json.loads(args.benchmark.read_bytes())
        assert check_benchmark(benchmark, audit, raw)
    else:
        assert check_audit(audit)
    result = dict(passed=True, ordinary_calls=16, scaling_calls=len(audit['scaling']),
        general_quasipolynomial=False, discovery_used=False,
        outcomes={arm: [r['arms'][arm]['result']['status'] for r in audit['records']] for arm in ARMS},
        source_files=len(audit['source_sha256']))
    if benchmark is not None:
        result.update(benchmark_cases=5, timed_and_warmup_calls=50,
            eligible_cases=[r['id'] for r in benchmark['records'] if r['summary']['eligible_common_complete_outcome']])
    if args.output:
        args.output.write_bytes(canonical_bytes(result)+b'\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
