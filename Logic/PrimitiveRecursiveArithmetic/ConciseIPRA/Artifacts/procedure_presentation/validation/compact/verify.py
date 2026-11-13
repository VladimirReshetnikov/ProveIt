"""Offline compact-codec and procedure composition checks."""
import ast
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from translate_shared import translate, load_kernel

ROOT = Path(__file__).resolve().parent
NAMES = [
    'computation_zero_local', 'computation_successor_local',
    'transport_reflexivity_local', 'zero_symmetry_one_local',
    'zero_symmetry_computable_zero_local', 'zero_symmetry_all_numbers_local',
    'derived_zero_source_equational_transport_local',
    'guarded_literal_equation_introduction_local', 'guarded_lift_elimination_local',
    'guarded_induction_with_used_hypothesis_local',
    'compound_case_introduction_local', 'compound_implication_elimination_local',
]


def run(path, certificate, optimized=False):
    result = subprocess.run([sys.executable, *(['-O'] if optimized else []), str(path)],
                            input=json.dumps(certificate), text=True,
                            capture_output=True, timeout=15)
    return result.returncode == 0 and result.stdout == 'ACCEPT\n'


def execution(namespace, certificate):
    stack = copy.deepcopy(certificate)
    header = stack.pop()
    events = []

    def packet():
        value = stack.pop()
        events.append(copy.deepcopy(value))
        return value

    namespace['q'] = packet
    try:
        namespace['c']([0], *header)
        outcome = 'returned'
    except BaseException as error:
        outcome = type(error).__name__
    return outcome, events, stack


def main():
    (ROOT / 'fixtures').mkdir(exist_ok=True)
    results, proofs = [], []
    for name in NAMES:
        source = json.loads((ROOT / 'fixtures_original' /
                             ('compact_context__' + name + '.json')).read_text())
        target = translate(source)
        (ROOT / 'fixtures' / (name + '.json')).write_text(json.dumps(target) + '\n')
        proofs.append((name, target))
        for optimized in (False, True):
            for checker, data in [('controls/offset472.py', source),
                                  ('controls/offset_shared468.py', target),
                                  ('code/checker_compact462.py', target)]:
                actual = run(ROOT / checker, data, optimized)
                results.append(dict(checker=checker, case=name, optimized=optimized,
                                    expected=True, actual=actual))
        bad = copy.deepcopy(target)
        bad[-1][0] = [0, [0]]
        for optimized in (False, True):
            for checker in ('controls/offset_shared468.py', 'code/checker_compact462.py'):
                actual = run(ROOT / checker, bad, optimized)
                results.append(dict(checker=checker, case='false_goal_' + name,
                                    optimized=optimized, expected=False, actual=actual))
    left = load_kernel(ROOT / 'controls/offset_shared468.py')
    right = load_kernel(ROOT / 'code/checker_compact462.py')
    comparisons, packets = [], 0
    for name, certificate in proofs:
        a, b = execution(left, certificate), execution(right, certificate)
        comparisons.append(dict(case=name, equal=a == b, packets=len(a[1])))
        packets += len(a[1])
    summary = {'python': sys.version, 'executions': len(results),
               'unexpected': [row for row in results if row['actual'] != row['expected']],
               'translated_certificates': len(proofs), 'exact_trace_comparisons': comparisons,
               'compared_packet_events': packets, 'results': results}
    (ROOT / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({key: value for key, value in summary.items() if key != 'results'}, indent=2))
    if summary['unexpected'] or not all(row['equal'] for row in comparisons):
        raise SystemExit('Failed compact verification')


if __name__ == '__main__':
    main()
