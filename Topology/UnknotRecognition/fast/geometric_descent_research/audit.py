"""Fourteen fresh whole-diagram calls comparing explicit cochain and geometry policies.

Run only after source freeze. Every returned result is saved before independent
replay. Hard native caps govern calls; no wall cutoff or status filtering hides
partial outcomes. Failed/interrupted runs retain exact incomplete coverage.
"""
import argparse
import json
from pathlib import Path

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_search import recognize_by_crushing
from .common import ARMS, cases, configs, digest, save, source_hashes
from .check_evidence import compare_endpoints, replay_result, check_audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    before = source_hashes()
    definitions = cases()
    options = {arm: configs(arm) for arm in ARMS}
    output = dict(schema='geometric-descent-audit-v1', passed=False,
        source_sha256=before, config=options, case_order=[c['id'] for c in definitions],
        records=[], wall_limit_seconds=None, unreturned_calls=[], failures=[],
        active_call=None,
        coverage=dict(ordinary_calls_expected=14, ordinary_calls_completed=0))
    save(args.output, output)
    for case in definitions:
        diagram = Diagram.from_pd(case['input_pd'])
        record = dict(case, input_pd_sha256=digest(case['input_pd']), arms={}, endpoint_comparison=None)
        output['records'].append(record)
        for arm in ARMS:
            output['active_call'] = dict(id=case['id'], arm=arm, returned=False)
            save(args.output, output)
            print(json.dumps(dict(start=output['active_call']), separators=(',', ':')), flush=True)
            try:
                result = recognize_by_crushing(diagram, **options[arm])
                record['arms'][arm] = dict(result=result, replay=None)
                output['active_call']['returned'] = True
                save(args.output, output)
                record['arms'][arm]['replay'] = replay_result(diagram, arm, result, options[arm])
                assert source_hashes() == before, 'source changed during audit'
            except BaseException as error:
                failure = dict(output['active_call'], work_complete=False,
                    error_type=type(error).__name__, message=str(error))
                output['failures'].append(failure)
                if not failure['returned']:
                    output['unreturned_calls'].append(failure)
                save(args.output, output)
                raise
            output['coverage']['ordinary_calls_completed'] += 1
            output['active_call'] = None
            save(args.output, output)
            print(json.dumps(dict(id=case['id'], arm=arm, status=result['status'],
                                  stats=result['stats']), separators=(',', ':')), flush=True)
        try:
            record['endpoint_comparison'] = compare_endpoints(record['arms'])
        except BaseException as error:
            output['failures'].append(dict(id=case['id'], phase='endpoint-comparison',
                returned=True, work_complete=False, error_type=type(error).__name__, message=str(error)))
            save(args.output, output)
            raise
        save(args.output, output)
    try:
        assert output['coverage']['ordinary_calls_completed'] == 14
        assert source_hashes() == before
        output['passed'] = True
        assert check_audit(output)
    except BaseException as error:
        output['passed'] = False
        output['failures'].append(dict(phase='final-replay', returned=True, work_complete=False,
            error_type=type(error).__name__, message=str(error)))
        save(args.output, output)
        raise
    save(args.output, output)
    print('PASSED', flush=True)


if __name__ == '__main__':
    main()
