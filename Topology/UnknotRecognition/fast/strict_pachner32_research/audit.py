"""Retain all eight bounded whole-diagram calls and separate archived replay.

Run after source freeze. Hard native caps govern every call; no arbitrary wall
cutoff or status filtering removes a returned result. Interrupted files retain
passed=False and exact incomplete coverage.
"""
import argparse
import json
from pathlib import Path

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_search import recognize_by_crushing
from .common import ARMS, cases, configs, digest, save, source_hashes
from .check_evidence import replay_archives, replay_result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    before = source_hashes()
    definitions = cases()
    options = {arm: configs(arm) for arm in ARMS}
    output = dict(schema='strict-pachner32-audit-v1', passed=False,
        source_sha256=before, config=options, case_order=[c['id'] for c in definitions],
        records=[], wall_limit_seconds=None, unreturned_calls=[], archival_replay=None,
        coverage=dict(ordinary_calls_expected=8, ordinary_calls_completed=0))
    save(args.output, output)
    output['archival_replay'] = replay_archives()
    assert source_hashes() == before, 'source changed during archival replay'
    save(args.output, output)
    for case in definitions:
        diagram = Diagram.from_pd(case['input_pd'])
        record = dict(case, input_pd_sha256=digest(case['input_pd']), arms={})
        output['records'].append(record)
        for arm in ARMS:
            save(args.output, output)
            try:
                result = recognize_by_crushing(diagram, **options[arm])
            except BaseException as error:
                output['unreturned_calls'].append(dict(id=case['id'], arm=arm,
                    work_complete=False, error_type=type(error).__name__))
                save(args.output, output)
                raise
            replay = replay_result(diagram, arm, result, options[arm])
            record['arms'][arm] = dict(result=result, replay=replay)
            output['coverage']['ordinary_calls_completed'] += 1
            assert source_hashes() == before, 'source changed during audit'
            save(args.output, output)
            print(json.dumps(dict(id=case['id'], arm=arm, status=result['status'],
                                  stats=result['stats']), separators=(',', ':')), flush=True)
    assert output['coverage']['ordinary_calls_completed'] == 8
    assert source_hashes() == before
    output['passed'] = True
    save(args.output, output)
    print('PASSED', flush=True)


if __name__ == '__main__':
    main()
