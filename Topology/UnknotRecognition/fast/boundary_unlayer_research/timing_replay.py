"""Solver-free coverage, source binding and ratio checks for paired timings."""
import argparse
from hashlib import sha256
import json
from math import isfinite
from pathlib import Path
from statistics import median

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from .common import (BENCHMARK_PROTOCOL, benchmark_bindings, normalized_result,
                     source_hashes, digest, diagram_options, SEARCH_CONFIGS)
from .replay import replay, replay_reduction


def replay_timings(data, audit, audit_bytes):
    replay(audit)
    pins = source_hashes()
    assert data['schema'] == 'boundary-unlayer-benchmark-v1' and data['passed'] is True
    assert data['source_sha256'] == pins and data['protocol'] == BENCHMARK_PROTOCOL
    assert data['audit_sha256'] == sha256(audit_bytes).hexdigest()
    cases = benchmark_bindings(audit)
    assert [(r['kind'], r['id']) for r in data['records']] == [(r['kind'], r['id']) for r in cases]
    count = 0
    for index, (record, case) in enumerate(zip(data['records'], cases)):
        assert len(record['warmups']) == 2
        assert [s['peel'] for s in record['warmups']] == [False, True]
        assert len(record['paired']) == BENCHMARK_PROTOCOL['paired_rounds']
        assert record['aa']['order'] == ['baseline_a', 'baseline_b']
        assert len(record['aa']['samples']) == 2 and not any(s['peel'] for s in record['aa']['samples'])
        samples = list(record['warmups'])+record['aa']['samples']
        for k, pair in enumerate(record['paired']):
            assert pair['round'] == k
            assert pair['order'] == (['baseline', 'peel'] if (index+k) % 2 == 0 else ['peel', 'baseline'])
            assert set(pair['samples']) == {'baseline', 'peel'}
            assert pair['samples']['baseline']['peel'] is False and pair['samples']['peel']['peel'] is True
            samples.extend(pair['samples'].values())
        for sample in samples:
            assert type(sample['peel']) is bool
            assert type(sample['serialized_bytes']) is int and sample['serialized_bytes'] > 0
            assert type(sample['seconds']) in (int, float) and isfinite(sample['seconds']) and sample['seconds'] > 0
            normalized = normalized_result(sample['result'])
            payload = json.dumps(normalized, sort_keys=True, separators=(',', ':')).encode()
            checksum = sha256(payload).hexdigest()
            expected = digest(normalized_result(case['arms']['peel' if sample['peel'] else 'baseline']))
            assert sample['serialized_bytes'] == len(payload) and sample['result_sha256'] == checksum
            assert sample['expected_audit_sha256'] == expected
            assert sample['matches_audit'] is (checksum == expected)
            result = sample['result']
            if case['kind'] == 'supplied':
                assert result['source'] == case['source'] and result['peel'] == sample['peel']
                assert result['method'] == 'dfs'
                assert result['search_config'] == SEARCH_CONFIGS['dfs']
                outcome = result['outcome'] if result['outcome'] != 'INCONCLUSIVE' else None
                if outcome is None:
                    replay_reduction(result)
            else:
                answer = result['result']
                assert result['options'] == diagram_options(peel=sample['peel'])
                outcome = answer['status'] if answer['status'] != 'INCONCLUSIVE' else None
                if outcome is None and 'partial_chain' in answer:
                    assert verify_crushing_chain(Diagram.from_pd(case['input_pd']), answer['partial_chain'])
                elif outcome is None:
                    assert answer['unreturned_recognition'] is True and answer['work_complete'] is False
                    assert 'wall limit' in answer['reason']
            assert sample['outcome'] == outcome
            if outcome is not None:
                # Full normalized equality binds every proof and work field
                # to an already independently replayed source-specific arm.
                assert checksum == expected
                assert normalized == normalized_result(case['arms']['peel' if sample['peel'] else 'baseline'])
            count += 1
        eligible = all(all(s['outcome'] is not None and s['matches_audit'] for s in p['samples'].values())
                       and p['samples']['baseline']['outcome'] == p['samples']['peel']['outcome'] for p in record['paired'])
        ratios = [p['samples']['baseline']['seconds']/p['samples']['peel']['seconds'] for p in record['paired']] if eligible else []
        assert record['summary']['eligible_complete_comparison'] is eligible
        assert record['summary']['paired_ratios'] == ratios
        assert record['summary']['median_paired_baseline_over_peel'] == (median(ratios) if ratios else None)
        assert record['summary']['aa_ratio'] == record['aa']['samples'][0]['seconds']/record['aa']['samples'][1]['seconds']
    assert source_hashes() == pins
    return dict(passed=True, cases=len(cases), samples=count, regina_used=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', type=Path, required=True)
    parser.add_argument('--benchmark', type=Path, required=True)
    args = parser.parse_args()
    raw = args.audit.read_bytes()
    print(json.dumps(replay_timings(json.loads(args.benchmark.read_text()), json.loads(raw), raw), sort_keys=True))


if __name__ == '__main__':
    main()
