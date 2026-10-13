"""Predeclared 50-call whole-diagram cochain versus geometric first-descent comparison, no wall cutoff."""
import argparse
from importlib import import_module
from hashlib import sha256
import json
from pathlib import Path
import platform
import sys
from time import perf_counter_ns

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_search import recognize_by_crushing
from .common import (ARMS, BENCHMARK_PROTOCOL, canonical_bytes, configs, digest,
                     save, source_hashes)
from .check_evidence import check_audit, eligible_benchmark, replay_result, timing_summary

PRODUCERS = {arm: recognize_by_crushing for arm in ARMS}


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
        'normal_pachner_descent', 'normal_pachner_descent_verify',
        'normal_geometric_descent', 'normal_geometric_descent_verify',
        'pachner23', 'pachner23_verify',
        'pachner_cover_search', 'pachner_cover_verify', 'pachner_cover_oracle',
    ):
        import_module('fastunknot.'+name)


def run_sample(diagram, arm, expected, *, capture=None):
    options = configs(arm)
    imported = {name for name in sys.modules if name.startswith('fastunknot.')}
    started = perf_counter_ns()
    result = PRODUCERS[arm](diagram, **options)
    if capture is not None:
        capture.update(returned=True, result=result)
    replay = replay_result(diagram, arm, result, options)
    if capture is not None:
        capture['replay'] = replay
    payload = canonical_bytes(result)
    checksum = sha256(payload).hexdigest()
    elapsed = perf_counter_ns()-started
    assert imported == {name for name in sys.modules if name.startswith('fastunknot.')}, 'native module initialized inside timer'
    sample = dict(elapsed_ns=elapsed, status=result['status'],
                  result_sha256=checksum, serialized_bytes=len(payload))
    sample.update(result=result, replay=replay)
    if capture is not None:
        capture['sample'] = sample
    assert checksum == expected, 'timed result differs from the full audited result'
    return sample


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    raw = args.audit.read_bytes()
    audit = json.loads(raw)
    before = source_hashes()
    indexed = {r['id']: r for r in audit['records']}
    output = dict(schema='geometric-descent-benchmark-v1', passed=False,
        source_sha256=before, audit_sha256=sha256(raw).hexdigest(),
        protocol=BENCHMARK_PROTOCOL, config={arm: configs(arm) for arm in ARMS}, python=sys.version,
        platform=platform.platform(), records=[], calls_completed=0, unreturned_calls=[],
        failures=[], active_call=None)
    save(args.output, output)
    try:
        assert check_audit(audit) and eligible_benchmark(audit)
        preload_native()
        assert audit['source_sha256'] == before == source_hashes()
    except BaseException as error:
        output['failures'].append(dict(phase='preflight', returned=False, work_complete=False,
            error_type=type(error).__name__, message=str(error)))
        save(args.output, output)
        raise
    for case_index, name in enumerate(BENCHMARK_PROTOCOL['case_ids']):
        case = indexed[name]
        # Imports, validated PD preparation and expected-result serialization
        # occur outside the timer. Every new recognition and replay is inside.
        diagram = Diagram.from_pd(case['input_pd'])
        expected = {arm: digest(case['arms'][arm]['result']) for arm in ARMS}
        record = dict(id=name, input_pd_sha256=case['input_pd_sha256'],
                      warmups={}, paired=[], aa=dict(arm='cochain', samples=[]))
        output['records'].append(record)

        def sample(arm, phase):
            capture = dict(returned=False)
            output['active_call'] = dict(id=name, arm=arm, phase=phase)
            save(args.output, output)
            try:
                answer = run_sample(diagram, arm, expected[arm], capture=capture)
            except BaseException as error:
                failure = dict(output['active_call'], **capture, work_complete=False,
                    error_type=type(error).__name__, message=str(error))
                output['failures'].append(failure)
                if not capture['returned']:
                    output['unreturned_calls'].append(failure)
                save(args.output, output)
                raise
            output['calls_completed'] += 1
            output['active_call'] = None
            return answer

        for arm in ARMS:
            record['warmups'][arm] = sample(arm, 'warmup')
            save(args.output, output)
        for round_index in range(BENCHMARK_PROTOCOL['paired_rounds']):
            order = list(ARMS if (case_index+round_index) % 2 == 0 else reversed(ARMS))
            pair = dict(round=round_index, order=order, samples={})
            record['paired'].append(pair)
            for arm in order:
                pair['samples'][arm] = sample(arm, 'pair-'+str(round_index))
                save(args.output, output)
        for i in range(2):
            record['aa']['samples'].append(sample('cochain', 'AA-'+str(i)))
            save(args.output, output)
        try:
            record['summary'] = timing_summary(record)
            assert source_hashes() == before
        except BaseException as error:
            output['failures'].append(dict(id=name, phase='case-finalization',
                returned=True, work_complete=False, error_type=type(error).__name__, message=str(error)))
            save(args.output, output)
            raise
        save(args.output, output)
        print(json.dumps(dict(id=name, summary=record['summary']), separators=(',', ':')), flush=True)
    try:
        assert output['calls_completed'] == BENCHMARK_PROTOCOL['total_calls'] == 50
        assert source_hashes() == before
    except BaseException as error:
        output['failures'].append(dict(phase='finalization', returned=True, work_complete=False,
            error_type=type(error).__name__, message=str(error)))
        save(args.output, output)
        raise
    output['passed'] = True
    save(args.output, output)
    print('PASSED', flush=True)


if __name__ == '__main__':
    main()
