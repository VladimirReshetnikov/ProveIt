"""Full returned workloads for eight diagrams under raw and factored crushing.

There is no arbitrary wall cutoff. Native hard finite work caps govern every
call. Each returned proof or partial result is independently replayed. Run only
after source freeze; interrupted files retain passed=False and exact coverage.
"""
import argparse
import json
from pathlib import Path

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_search import recognize_by_crushing
from fastunknot.factored_crushing import recognize_factored_by_crushing
from .common import ARMS, cases, configs, digest, repeated_trefoils, save, source_hashes
from .check_evidence import replay_result


PRODUCERS = dict(raw=recognize_by_crushing, factored=recognize_factored_by_crushing)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--scaling', action='store_true',
                        help='Also run the wrapper alone on 2,4,8,16 visible trefoil factors.')
    args = parser.parse_args()
    before = source_hashes()
    definitions = cases()
    options = configs()
    output = dict(schema='factored-crushing-audit-v1', passed=False,
        source_sha256=before, config=options, case_order=[c['id'] for c in definitions],
        records=[], scaling=[], scaling_requested=args.scaling,
        wall_limit_seconds=None, unreturned_calls=[],
        coverage=dict(ordinary_calls_expected=16, ordinary_calls_completed=0,
                      scaling_calls_expected=4 if args.scaling else 0, scaling_calls_completed=0))
    save(args.output, output)
    for case in definitions:
        diagram = Diagram.from_pd(case['input_pd'])
        record = dict(case, input_pd_sha256=digest(case['input_pd']), arms={})
        output['records'].append(record)
        for arm in ARMS:
            save(args.output, output)
            try:
                result = PRODUCERS[arm](diagram, **options)
            except BaseException as error:
                output['unreturned_calls'].append(dict(id=case['id'], arm=arm,
                    work_complete=False, error_type=type(error).__name__))
                save(args.output, output)
                raise
            replay = replay_result(diagram, arm, result, options)
            record['arms'][arm] = dict(result=result, replay=replay)
            output['coverage']['ordinary_calls_completed'] += 1
            assert source_hashes() == before, 'source changed during audit'
            save(args.output, output)
            print(json.dumps(dict(id=case['id'], arm=arm, status=result['status'],
                                  stats=result['stats']), separators=(',', ':')), flush=True)
    if args.scaling:
        for k in (2, 4, 8, 16):
            case = repeated_trefoils(k)
            diagram = Diagram.from_pd(case['input_pd'])
            try:
                result = recognize_factored_by_crushing(diagram, **options)
            except BaseException as error:
                output['unreturned_calls'].append(dict(id=case['id'], arm='factored',
                    work_complete=False, error_type=type(error).__name__))
                save(args.output, output)
                raise
            replay = replay_result(diagram, 'factored', result, options)
            output['scaling'].append(dict(case, input_pd_sha256=digest(case['input_pd']),
                                         result=result, replay=replay))
            output['coverage']['scaling_calls_completed'] += 1
            assert source_hashes() == before
            save(args.output, output)
            print(json.dumps(dict(id=case['id'], arm='factored', status=result['status'],
                                  stats=result['stats']), separators=(',', ':')), flush=True)
    assert source_hashes() == before
    output['passed'] = True
    save(args.output, output)
    print('PASSED', flush=True)


if __name__ == '__main__':
    main()
