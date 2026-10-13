"""Predeclared 30-call whole-diagram strict Pachner preprocessing comparison, no wall cutoff."""
import argparse
from importlib import import_module
from hashlib import sha256
import json
from pathlib import Path
import platform
from statistics import median
import sys
from time import perf_counter_ns

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_search import recognize_by_crushing
from .common import (ARMS, BENCHMARK_PROTOCOL, canonical_bytes, configs, digest,
                     save, source_hashes)
from .check_evidence import check_audit, replay_result

PRODUCERS = dict(baseline=recognize_by_crushing, pachner32=recognize_by_crushing)


# The native driver deliberately imports producers inside its private function
# to keep verification independent. Initialize this selected backend's modules
# before starting any timer; the in-function cached imports then do no loading.
def preload_native():
    for name in (
        'diagram_exterior', 'diagram_exterior_verify', 'boundary_shellings',
        'boundary_shellings_verify', 'normal_crushing', 'normal_crushing_verify',
        'normal_sector', 'sector_matching_support', 'normal_surface_geometry',
        'normal_euler', 'positive_ray', 'normal_vertex_reduction',
        'normal_euler_tree', 'normal_euler_transversal', 'boundary_unlayer',
        'boundary_unlayer_verify', 'bounded_lp', 'source_kernel',
        'normal_pachner32', 'normal_pachner32_verify', 'pachner32', 'pachner32_verify',
    ):
        import_module('fastunknot.'+name)


def run_sample(diagram, arm, expected, *, keep_result=False):
    options = configs(arm)
    imported = {name for name in sys.modules if name.startswith('fastunknot.')}
    started = perf_counter_ns()
    result = PRODUCERS[arm](diagram, **options)
    replay = replay_result(diagram, arm, result, options)
    payload = canonical_bytes(result)
    checksum = sha256(payload).hexdigest()
    elapsed = perf_counter_ns()-started
    assert imported == {name for name in sys.modules if name.startswith('fastunknot.')}, 'native module initialized inside timer'
    sample = dict(elapsed_ns=elapsed, status=result['status'],
                  result_sha256=checksum, serialized_bytes=len(payload))
    if keep_result:
        sample.update(result=result, replay=replay)
    assert checksum == expected, 'timed result differs from the full audited result'
    return sample


def summarize(record):
    all_samples = list(record['warmups'].values())
    all_samples += [s for pair in record['paired'] for s in pair['samples'].values()]
    all_samples += record['aa']['samples']
    statuses = {sample['status'] for sample in all_samples}
    eligible = len(statuses) == 1 and statuses <= {'UNKNOT', 'KNOTTED'}
    ratios = [pair['samples']['baseline']['elapsed_ns']/pair['samples']['pachner32']['elapsed_ns']
              for pair in record['paired']] if eligible else []
    return dict(eligible_common_complete_outcome=eligible,
        common_status=next(iter(statuses)) if eligible else None,
        paired_baseline_over_pachner32=ratios,
        median_paired_baseline_over_pachner32=median(ratios) if ratios else None,
        median_ns={arm: median([p['samples'][arm]['elapsed_ns'] for p in record['paired']])
                   for arm in ARMS},
        aa_ratio=record['aa']['samples'][0]['elapsed_ns']/record['aa']['samples'][1]['elapsed_ns'],
        outcome_scope='Same completed whole-diagram verdict.' if eligible else
                      'Resource-bounded outcomes retained; no recognition speed ratio.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    raw = args.audit.read_bytes()
    audit = json.loads(raw)
    assert check_audit(audit)
    preload_native()
    before = source_hashes()
    assert audit['source_sha256'] == before
    indexed = {r['id']: r for r in audit['records']}
    output = dict(schema='strict-pachner32-benchmark-v1', passed=False,
        source_sha256=before, audit_sha256=sha256(raw).hexdigest(),
        protocol=BENCHMARK_PROTOCOL, config={arm: configs(arm) for arm in ARMS}, python=sys.version,
        platform=platform.platform(), records=[], calls_completed=0, unreturned_calls=[])
    save(args.output, output)
    for case_index, name in enumerate(BENCHMARK_PROTOCOL['case_ids']):
        case = indexed[name]
        # Imports, validated PD preparation and expected-result serialization
        # occur outside the timer. Every new recognition and replay is inside.
        diagram = Diagram.from_pd(case['input_pd'])
        expected = {arm: digest(case['arms'][arm]['result']) for arm in ARMS}
        record = dict(id=name, input_pd_sha256=case['input_pd_sha256'],
                      warmups={}, paired=[], aa=dict(arm='baseline', samples=[]))
        output['records'].append(record)

        def sample(arm, phase, keep=False):
            try:
                answer = run_sample(diagram, arm, expected[arm], keep_result=keep)
            except BaseException as error:
                output['unreturned_calls'].append(dict(id=name, arm=arm, phase=phase,
                    work_complete=False, error_type=type(error).__name__))
                save(args.output, output)
                raise
            output['calls_completed'] += 1
            return answer

        for arm in ARMS:
            record['warmups'][arm] = sample(arm, 'warmup', keep=True)
            save(args.output, output)
        for round_index in range(BENCHMARK_PROTOCOL['paired_rounds']):
            order = list(ARMS if (case_index+round_index) % 2 == 0 else reversed(ARMS))
            pair = dict(round=round_index, order=order, samples={})
            record['paired'].append(pair)
            for arm in order:
                pair['samples'][arm] = sample(arm, 'pair-'+str(round_index))
                save(args.output, output)
        for i in range(2):
            record['aa']['samples'].append(sample('baseline', 'AA-'+str(i)))
            save(args.output, output)
        record['summary'] = summarize(record)
        assert source_hashes() == before
        save(args.output, output)
        print(json.dumps(dict(id=name, summary=record['summary']), separators=(',', ':')), flush=True)
    assert output['calls_completed'] == BENCHMARK_PROTOCOL['total_calls'] == 30
    assert source_hashes() == before
    output['passed'] = True
    save(args.output, output)
    print('PASSED', flush=True)


if __name__ == '__main__':
    main()
