"""Finite integration checks and certificate comparisons, without kernel imports."""

import ast
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
CODE = ROOT.parent / 'code'


def producer(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def named_cases(p):
    cases = [c for c in p.build_cases() if 'proof_tree' in c]
    extra = [
        ('zero_base_direct', p.compute(p.I(0, 0, 'z', 0))),
        ('zero_predecessor_direct', p.compute(p.I(p.ONE, 0, 'z', p.S(p.V('z'))))),
        ('zero_reflexivity', p.reflexivity(0)),
    ]
    closed_zero = p.I(p.TWO, p.ONE, 'v', 0)
    equality = p.symmetry(p.compute(closed_zero))
    extra.append(('literal_zero_transport_source',
                  p.transport(equality, 'x', p.Eq(p.V('x'), 0), p.reflexivity(0))))
    for name, proof in extra:
        emitter = p.Emitter()
        cases.append({'name': name, 'accept': True,
                      'packet': emitter.packet(proof), 'trace': emitter.trace})
    return cases


def extra_controls(cases, zero, constructed):
    result = []

    def add(name, packet, expected=False):
        result.append({'name': name, 'packet': packet, 'accept': expected})

    valid = next(c for c in cases if c['name'] == 'zero_base_direct')['packet']
    add('inert_prefix', [[{'unread': 'data'}], None] + copy.deepcopy(valid), True)
    bad = copy.deepcopy(valid)
    bad[-1] = [zero, [zero]]
    add('closed_false_goal', bad)
    bad = copy.deepcopy(valid)
    bad[-1] = [-999, -999]
    add('malicious_future_capture_goal', bad)
    for original, rule, field, name in [
        ('nonvacuous_witness_DE_roundtrip', 'DI', 3, 'future_witness'),
        ('Q_arbitrary_term_specialization', 'QE', 2, 'future_target'),
    ]:
        case = next(c for c in cases if c['name'] == original)
        bad = copy.deepcopy(case['packet'])
        event = next(e for e in case['trace'] if e['rule'] == rule)
        bad[event['packet_index']][field] = -999
        add(name, bad)
    case = next(c for c in cases if c['name'] == 'atomic_progress_closure')
    bad = copy.deepcopy(case['packet'])
    event = next(e for e in case['trace'] if e['rule'] == 'DI'
                 and e['mode'] == 'progress')
    bad[event['packet_index']][0] = []
    add('induction_replaced_by_base', bad)
    bad = copy.deepcopy(valid)
    bad[-1] = [bad[-1][0], [zero]]
    add('wrong_computation_target', bad)
    zterm = zero
    m = 1 if constructed else [zterm, [zterm]]
    minor = next(c for c in cases if c['name'] == 'zero_reflexivity')['packet']
    false_tr = copy.deepcopy(minor[:-1]) + [
        [m, zterm, [zterm], [zterm, 3]],
        [zterm, [zterm]],
    ]
    add('false_major_transport', false_tr)
    add('missing_update', [[0, 0, zterm or [zterm], None],
                           [[zterm, zterm, zterm], zterm]])
    add('unreadable_record', [[1, 2], [zterm, zterm]])
    return result


def run(program, payload, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(program)]
    completed = subprocess.run(command, input=payload, text=True,
                               capture_output=True, timeout=15)
    return completed.returncode == 0 and completed.stdout == 'ACCEPT\n'


def main():
    producers = {
        'old': producer('producer_old_local'),
        'zero': producer('producer_zero_only_local'),
        'constructed': producer('producer_zero1_local'),
    }
    cases = {family: named_cases(p) for family, p in producers.items()}
    profiles = [
        ('control_compact.py', 'old'),
        ('control_explicit.py', 'old'),
        ('checker_zero_compact.py', 'zero'),
        ('checker_zero_explicit.py', 'zero'),
        ('checker_constructed_compact.py', 'constructed'),
        ('checker_constructed_explicit.py', 'constructed'),
        ('checker_readable.py', 'constructed'),
    ]
    rows = []
    fixtures = ROOT.parent / 'examples'
    for family, data in cases.items():
        directory = fixtures / family
        directory.mkdir(parents=True, exist_ok=True)
        tests = data + extra_controls(data, 0 if family == 'old' else 1,
                                      family == 'constructed')
        for case in tests:
            (directory / (case['name'] + '.json')).write_text(
                json.dumps(case['packet'], indent=2) + '\n')
        cases[family] = tests

    malformed = ['', '{', 'null', '{}', '[]', '["x"]', '[["x"], [1,1]]']
    for filename, family in profiles:
        for optimized in [False, True]:
            for case in cases[family]:
                accepted = run(CODE / filename, json.dumps(case['packet']), optimized)
                rows.append({'program': filename, 'optimized': optimized,
                             'case': case['name'], 'expected': case['accept'],
                             'accepted': accepted, 'pass': accepted == case['accept']})
            for number, payload in enumerate(malformed):
                accepted = run(CODE / filename, payload, optimized)
                rows.append({'program': filename, 'optimized': optimized,
                             'case': 'malformed_' + str(number), 'expected': False,
                             'accepted': accepted, 'pass': not accepted})

    # Two changes that destroy a material inference guard must admit their
    # corresponding forged proof. The originals must reject the same packet.
    source = (CODE / 'checker_constructed_compact.py').read_text()
    tree = ast.parse(source)
    for node in ast.walk(tree):
        if isinstance(node, ast.If) and isinstance(node.test, ast.Name) \
                and node.test.id == 'm':
            call = node.body[0].value
            assignment = call.args[0]
            node.body[0] = ast.Assign(targets=[assignment.target],
                                      value=assignment.value)
    no_major = ast.unparse(ast.fix_missing_locations(tree)) + '\n'
    no_restriction = source.replace('len(a) % 2 == m', 'True')
    mutation_rows = []
    with tempfile.TemporaryDirectory() as temporary:
        for name, mutated, case_name in [
            ('unchecked_major', no_major, 'false_major_transport'),
            ('unrestricted_progress', no_restriction, 'forbidden_compound_progress'),
        ]:
            path = Path(temporary) / (name + '.py')
            path.write_text(mutated)
            case = next(c for c in cases['constructed'] if c['name'] == case_name)
            for optimized in [False, True]:
                accepted = run(path, json.dumps(case['packet']), optimized)
                mutation_rows.append({'mutation': name, 'case': case_name,
                                      'optimized': optimized,
                                      'forged_proof_accepted': accepted})

    comparisons = []
    names = [c['name'] for c in cases['old'] if c.get('accept')
             and c['name'] in {d['name'] for d in cases['zero']}
             and not c['name'].startswith('neutral')
             and c['name'] != 'inert_prefix']
    for name in names:
        record = {'name': name}
        for family in ('old', 'zero', 'constructed'):
            packet = next(c['packet'] for c in cases[family] if c['name'] == name)
            record[family] = {
                'commands': len(packet) - 1,
                'json_bytes': len(json.dumps(packet, separators=(',', ':')).encode()),
            }
        comparisons.append(record)

    receipt = {'profile_runs': len(rows), 'passed': sum(r['pass'] for r in rows),
               'results': rows, 'mutation_controls': mutation_rows,
               'certificate_comparison': comparisons,
               'scope': 'Finite integration evidence, not a proof of universal soundness.'}
    (ROOT.parent / 'evidence' / 'validation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    failures = [r for r in rows if not r['pass']]
    print(json.dumps({'profile_runs': len(rows), 'passed': receipt['passed'],
                      'failures': failures, 'mutations': mutation_rows,
                      'certificate_comparison': comparisons}, indent=2))
    if failures or not all(r['forged_proof_accepted'] for r in mutation_rows):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
