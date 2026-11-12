"""Finite integration checks for an explicitly inherited kernel composition.

The named producer is untrusted and does not import any kernel.  A passing
finite test suite is not a proof of soundness or a proof-assistant artifact.
"""
import ast
import copy
import gzip
import hashlib
import io
import json
import platform
from pathlib import Path
import subprocess
import sys
import tempfile
import tokenize

import source_producer as producer
import source_test_profiles as inherited_tests
import global_source_producer

ROOT = Path(__file__).resolve().parent


def convert(packet):
    """Translate the inherited guarded absent-major and DI mode fields."""
    result = copy.deepcopy(packet)
    for record in result[:-1]:
        if not isinstance(record, list) or len(record) != 4:
            continue
        major, source, initial, body = record
        if not major:
            if not initial:
                record[2] = major
            record[0] = []
    return result


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw.decode())
    for item in ast.walk(tree):
        if isinstance(item, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if item.body and isinstance(item.body[0], ast.Expr):
                value = item.body[0].value
                if isinstance(value, ast.Constant) and isinstance(value.value, str):
                    item.body.pop(0)
    source = (ast.unparse(tree) + '\n').encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(token.type not in ignored
                 for token in tokenize.tokenize(io.BytesIO(source).readline))
    return {'file': path.name, 'raw_bytes': len(raw), 'normalized_bytes': len(source),
            'tokens': tokens, 'ast_nodes': sum(1 for _ in ast.walk(ast.parse(source))),
            'gzip9_raw_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
            'gzip9_normalized_bytes': len(gzip.compress(source, compresslevel=9, mtime=0)),
            'sha256': hashlib.sha256(raw).hexdigest()}


def run(path, payload, optimized=False):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
    result = subprocess.run(command, input=payload, text=True,
                            capture_output=True, timeout=15)
    return {'accepted': result.returncode == 0 and result.stdout == 'ACCEPT\n',
            'exit_status': result.returncode}


def build_cases():
    named = inherited_tests.named_cases(producer)
    old = named + inherited_tests.extra_controls(named, 0, False)
    seen = {case['name'] for case in old}
    for case in producer.build_cases():
        if case['name'] not in seen:
            old.append(case)
    new = []
    for case in old:
        new.append({'name': case['name'], 'accept': case['accept'],
                    'meaning': case.get('meaning', 'Inherited named proof or boundary control'),
                    'packet': convert(case['packet'])})
    # The copied old producer retains a historical null-major raw alias.
    # The exact guarded affine-or source instead evaluates None*3 and rejects.
    # Its neutral [] translation is a valid zero-instance alias and accepts.
    # Preserve this difference rather than silently rewriting the old packet.
    old = [dict(case, accept=False,
                comparison_note='Literal null major is not admitted by the guarded affine-or comparator')
           if case['name'] == 'out_of_range_seed_zero_alias' else case
           for case in old]

    def add(name, packet, expected, meaning):
        new.append({'name': name, 'packet': packet,
                    'accept': expected, 'meaning': meaning})

    add('empty_array_truth', [[]], True, 'The initial empty-array truth premise.')
    for value, name in [(0, 'zero'), (False, 'boolean_false'), (0.0, 'float_zero'),
                        (True, 'boolean_true'), (-1, 'negative_scalar')]:
        add('scalar_goal_' + name, [value], False,
            'No numeric goal has a finite successful proof in a list-only context.')
        add('scalar_major_' + name, [[value, [0], 0, 0], [0, [0]]], False,
            'A forbidden scalar major cannot reach the unguarded endpoint matcher.')
    add('fresh_parameter_goal', [[[], 0, -1, 0], [[0, -1, 0], -1]], False,
        'Closed input cannot mention the next unallocated parameter.')
    # A direct source construction must remain an actual successor source.
    proof = producer.compute(producer.I(producer.TWO, producer.ONE,
                                       'source_state', producer.S(producer.V('source_state'))))
    packet = convert(producer.Emitter().packet(proof))
    packet[-1][0][0] = packet[-1][0][0][0]
    add('forged_successor_source', packet, False,
        'Forcing the generated source counter to be its predecessor gives a false equation.')
    return old, new


def main():
    old, cases = build_cases()
    (ROOT / 'cases.json').write_text(json.dumps({'cases': cases}, indent=2) + '\n')
    (ROOT / 'fixtures').mkdir(exist_ok=True)
    for case in cases:
        (ROOT / 'fixtures' / (case['name'] + '.json')).write_text(
            json.dumps(case['packet'], indent=2) + '\n')
    malformed = ['', '{', 'null', '{}', '[]', '["x"]', '[["x"], [0,0]]',
                 '[NaN]', '[Infinity]', '[{}]', '[""]', '[] []']
    profiles = [('checker_compact.py', cases), ('checker_explicit.py', cases),
                ('ablation_conditional_local.py', cases),
                ('ablation_guarded_local.py', old)]
    global_cases = [dict(case, packet=convert(case['packet']))
                    for case in inherited_tests.named_cases(global_source_producer)]
    profiles.append(('ablation_neutral_global.py', global_cases))
    rows = []
    for filename, tests in profiles:
        for optimized in (False, True):
            for case in tests:
                result = run(ROOT / filename, json.dumps(case['packet']), optimized)
                rows.append({'profile': filename, 'optimized': optimized,
                             'case': case['name'], 'expected': case['accept'], **result,
                             'pass': result['accepted'] == case['accept']})
            for index, payload in enumerate(malformed):
                result = run(ROOT / filename, payload, optimized)
                rows.append({'profile': filename, 'optimized': optimized,
                             'case': 'malformed_' + str(index), 'expected': False, **result,
                             'pass': not result['accepted']})

    index = {case['name']: case for case in cases}
    source = (ROOT / 'checker_compact.py').read_text()
    changes = [
        ('mandatory_major', '    c(m, g, k)\n', '', 'false_major_transport', True),
        ('atomic_only_progress', 'len(a) % 2 == u', 'True', 'forbidden_compound_progress', True),
        ('closed_goal_scope', 'k <= a < d', 'a < d', 'fresh_parameter_goal', True),
        ('successor_source', 's and [s]', 's', 'forged_successor_source', True),
        ('major_receives_local_floor', 'c(m, g, k)', 'c(m, g)',
         'contextual_induction_seed_congruence', False),
    ]
    controls = []
    with tempfile.TemporaryDirectory() as temporary:
        for name, before, after, case_name, expected_mutant in changes:
            if source.count(before) != 1:
                raise RuntimeError('Mutation target must be unique: ' + name)
            path = Path(temporary) / (name + '.py')
            path.write_text(source.replace(before, after))
            case = index[case_name]
            for optimized in (False, True):
                original = run(ROOT / 'checker_compact.py', json.dumps(case['packet']), optimized)
                mutant = run(path, json.dumps(case['packet']), optimized)
                controls.append({'name': name, 'case': case_name, 'optimized': optimized,
                                 'original': original, 'mutant': mutant,
                                 'pass': original['accepted'] == case['accept']
                                         and mutant['accepted'] == expected_mutant})

    metrics = [measure(ROOT / filename) for filename in [
        'checker_compact.py', 'checker_explicit.py', 'ablation_guarded_local.py',
        'ablation_neutral_global.py', 'ablation_conditional_local.py']]
    receipt = {'python': platform.python_version(), 'cases': len(cases),
               'runs': len(rows), 'passed': sum(row['pass'] for row in rows),
               'results': rows, 'mutation_controls': controls, 'metrics': metrics,
               'raw_interface_difference': 'The copied producer out_of_range_seed_zero_alias has a null major. The exact guarded affine-or comparator rejects None*3; the neutral [] translation accepts the valid zero-instance alias.',
               'scope': 'Finite executable evidence, not a universal soundness proof.'}
    (ROOT / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    (ROOT / 'metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
    failures = [row for row in rows + controls if not row['pass']]
    print(json.dumps({'runs': len(rows), 'passed': receipt['passed'],
                      'controls': len(controls), 'failures': failures, 'metrics': metrics}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
