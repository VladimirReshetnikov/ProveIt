"""Focused process-level tests for the REV proof producers and checkers.

No checker imports this harness or producer. Finite tests exercise actual
new derivations, source reversal, induction restrictions, and scope failures;
they do not prove universal soundness or the interpretation metatheorems.
"""
import argparse
import copy
import hashlib
import json
import platform
import subprocess
import sys
from pathlib import Path

import rev_producer as r

ROOT = Path(__file__).resolve().parent


def make_cases():
    cases = r.fixtures()
    named = {case['name']: case for case in cases}
    def add(name, packet, meaning, *, accept=False, typed_only=False):
        cases.append({'name': name, 'packet': packet, 'meaning': meaning,
                      'accept': accept, 'typed_only': typed_only,
                      'goal_kind': 'eq', 'trace': []})
    add('canonical_false_without_proof', [[0, [0]]],
        'The canonical contradiction 0=1 has no proof instructions.')
    emitter = r.Emitter()
    anchor_packet = emitter.packet(r.zero_anchor())
    invalid = copy.deepcopy(anchor_packet)
    invalid[-1][1] = [0]
    add('wrong_computation_endpoint', invalid,
        'A genuine computation ending in zero cannot close the changed goal ending in one.')
    invalid = copy.deepcopy(named['root_reversal_zero_source']['packet'])
    first_x = next(e for e in named['root_reversal_zero_source']['trace'] if e['rule'] == 'X')
    command = invalid[first_x['packet_index']]
    command[0][1] = [0]
    command[2] = [0]
    add('unproved_elimination_major', invalid,
        'The major equation is changed from c=0 to c=1; it must still be proved.')
    invalid = copy.deepcopy(named['atomic_progress_Q_closure']['packet'])
    event = next(e for e in named['atomic_progress_Q_closure']['trace']
                 if e['rule'] == 'DI' and e['mode'] == 'progress')
    invalid[event['packet_index']][2] = []
    add('induction_hypothesis_replaced_by_base', invalid,
        'The genuine induction step loses E(z) when its mode changes to cases supplying E(0).')
    invalid = copy.deepcopy(named['QX_arbitrary_target']['packet'])
    event = next(e for e in named['QX_arbitrary_target']['trace'] if e['rule'] == 'QX')
    invalid[event['packet_index']][2] = -999
    add('unallocated_QX_target', invalid,
        'A QX target is replaced by a numerical label outside the allocated scope.')
    invalid = copy.deepcopy(named['nonvacuous_D_elimination']['packet'])
    event = next(e for e in named['nonvacuous_D_elimination']['trace'] if e['rule'] == 'DI')
    invalid[event['packet_index']][3] = -999
    add('unallocated_DI_witness', invalid,
        'The existential witness of a nonvacuous DI proof is replaced by an unallocated label.')
    add('free_label_in_closed_goal', [[-1, -1]],
        'A closed public goal cannot contain an unallocated free parameter.')
    add('out_of_scope_bound_slot', [[3, 3]],
        'At the root equation there is no numerical binder for slot 3.')
    add('empty_administrative_goal', [[]],
        'Administrative truth is not a public canonical formula.')
    add('four_child_public_goal', [[0, 0, 0, 0]],
        'Surplus-arity administrative padding is not a public canonical formula.')
    add('noncanonical_Q_goal', [[[0, 0], [0, [0]], [0, 0]]],
        'The public full-Q interface requires three equal copies of its matrix.')
    add('boolean_goal_alias', [[False, False]],
        'Booleans cannot alias numerical integer zero in a canonical goal.')
    add('float_goal_alias', [[0.0, 0.0]],
        'Floating-point numbers cannot alias numerical integer zero in a canonical goal.')
    valid = named['new_reflexivity_zero']['packet']
    add('unused_integer_prefix', [17] + copy.deepcopy(valid),
        'An unused well-typed integer prefix is inert.', accept=True)
    for label, prefix in [('boolean', True), ('float', 0.0), ('null', None),
                          ('string', 'inert'), ('mapping', {}),
                          ('nested_boolean', [0, [False]])]:
        add('unused_' + label + '_prefix', [prefix] + copy.deepcopy(valid),
            'The whole-JSON typed interface rejects this unused non-int/list data; '
            'the untyped core intentionally ignores an unused prefix.',
            accept=True, typed_only=True)
    return cases


def execute(path, packet, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
    result = subprocess.run(command, input=json.dumps(packet), text=True,
                            capture_output=True, timeout=15)
    accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
    return {'accepted': accepted, 'returncode': result.returncode,
            'stdout': result.stdout,
            'error_tail': result.stderr[-300:] if not accepted else ''}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkers-dir', type=Path,
                        help='Optional original working-tree checker directory; defaults to packaged profiles')
    parser.add_argument('--receipt', type=Path,
                        default=ROOT.parent / 'evidence/all_rev_reproduction.json')
    parser.add_argument('--single-checker', type=Path)
    parser.add_argument('--profile', choices=['eqd', 'full'], default='full')
    parser.add_argument('--zero-neutral', action='store_true')
    parser.add_argument('--typed', action='store_true')
    args = parser.parse_args()
    if args.single_checker:
        profiles = [(args.single_checker, args.zero_neutral, args.profile, args.typed)]
        control = None
    elif args.checkers_dir:
        directory = args.checkers_dir
        profiles = [
            (directory / 'rev_shared_strict_checker.py', False, 'eqd', False),
            (directory / 'rev_full_strict_checker.py', False, 'full', False),
            (directory / 'rev_strict_eqd_zero.py', True, 'eqd', False),
            (directory / 'rev_strict_full_zero.py', True, 'full', False),
            (directory / 'final/checker_rev_typed.py', True, 'full', True),
        ]
        control = directory / 'final/control_shared_typed.py'
    else:
        profiles = [
            (ROOT / 'profiles/rev_shared_strict_checker.py', False, 'eqd', False),
            (ROOT / 'profiles/rev_full_strict_checker.py', False, 'full', False),
            (ROOT.parent / 'code/checker_rev_strict_eqd.py', True, 'eqd', False),
            (ROOT.parent / 'code/checker_rev_strict_full.py', True, 'full', False),
            (ROOT.parent / 'code/checker_rev_typed.py', True, 'full', True),
        ]
        control = ROOT.parent / 'controls/control_shared_typed.py'
    missing = [str(path) for path, *_ in profiles if not path.is_file()]
    if control is not None and not control.is_file():
        missing.append(str(control))
    if missing:
        raise SystemExit('Missing checker files: ' + ', '.join(missing))
    cases = make_cases()
    fixture_dir = ROOT / 'certificates'
    fixture_dir.mkdir(exist_ok=True)
    (fixture_dir / 'zero_neutral').mkdir(exist_ok=True)
    metadata = []
    for case in cases:
        for target, packet in [(fixture_dir, case['packet']),
                               (fixture_dir / 'zero_neutral', r.zero_neutral(case['packet']))]:
            (target / (case['name'] + '.json')).write_text(
                json.dumps(packet, separators=(',', ':')) + '\n')
        metadata.append({key: value for key, value in case.items() if key not in ('packet', 'trace')}
                        | {'commands': len(case['packet']) - 1})
    (ROOT / 'cases.json').write_text(json.dumps(metadata, indent=2) + '\n')
    observations, failures, sources = [], [], []
    for path, use_zero, profile, typed in profiles:
        sources.append({'file': path.name,
                        'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                        'zero_neutral': use_zero, 'profile': profile, 'whole_json_typed': typed})
        for optimized in [False, True]:
            for case in cases:
                expected = case['accept']
                if profile == 'eqd' and case['goal_kind'] == 'q':
                    expected = False
                if typed and case.get('typed_only'):
                    expected = False
                packet = r.zero_neutral(case['packet']) if use_zero else case['packet']
                result = execute(path, packet, optimized)
                record = {'checker': path.name, 'optimized': optimized,
                          'case': case['name'], 'expected': expected} | result
                observations.append(record)
                if result['accepted'] != expected:
                    failures.append(record)
    # Matched controls verify that the exact REV orientation is tested.
    controls = []
    if control is not None:
        selected = next(c for c in cases if c['name'] == 'root_reversal_zero_source')
        for optimized in [False, True]:
            result = execute(control, r.zero_neutral(selected['packet']), optimized)
            record = {'checker': control.name, 'optimized': optimized,
                      'case': selected['name'], 'expected': False} | result
            controls.append(record)
            if result['accepted']:
                failures.append(record)
    receipt = {'status': 'PASS' if not failures else 'FAIL',
               'scope': 'Focused finite certificate and input-contract checks, not a metatheorem proof',
               'python': sys.version, 'platform': platform.platform(),
               'cases': len(cases), 'checker_profiles': sources,
               'observations': observations, 'matched_controls': controls,
               'failures': failures,
               'process_expectations': len(observations) + len(controls)}
    args.receipt.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': receipt['status'], 'cases': len(cases),
                      'process_expectations': receipt['process_expectations'],
                      'failures': len(failures), 'receipt': str(args.receipt)}))
    if failures:
        for failure in failures:
            print(json.dumps(failure))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
