#!/usr/bin/env python3
"""Differential validation of the four-byte public-scope refinement.

Run with `python3 verify.py` in any directory. Both complete standalone
modules are launched in normal and optimized Python. Finite tests supplement
the acceptance-equivalence proof in proof.txt; they do not prove it.
"""

import ast
import copy
import gzip
import hashlib
import io
import itertools
import json
import platform
import subprocess
import sys
import tokenize
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent


def source_functions(path):
    tree = ast.parse(path.read_text())
    functions = ast.Module(body=[n for n in tree.body if isinstance(n, ast.FunctionDef)], type_ignores=[])
    environment = {}
    exec(compile(functions, str(path), 'exec'), environment)
    return environment


def invoke(job):
    case, program, optimized, recursion_limit = job
    command = [sys.executable]
    if optimized:
        command.append('-O')
    if recursion_limit is None:
        command.append(str(HERE / program))
    else:
        command += ['-c', 'import runpy,sys;sys.setrecursionlimit(int(sys.argv[2]));runpy.run_path(sys.argv[1],run_name="__main__")', str(HERE / program), str(recursion_limit)]
    process = subprocess.run(command, input=case['raw'], text=True, capture_output=True, timeout=15)
    accepted = process.returncode == 0 and process.stdout == 'ACCEPT\n'
    return {
        'name': case['name'], 'program': program, 'optimized': optimized,
        'recursion_limit': recursion_limit, 'accepted': accepted,
        'expected': case.get('expected'), 'returncode': process.returncode,
        'recursion_error': 'RecursionError' in process.stderr,
        'json_decode_error': 'JSONDecodeError' in process.stderr,
    }


def main():
    old_path, new_path = HERE / 'control.py', HERE / 'checker.py'
    old_text = ast.unparse(ast.parse(old_path.read_text())) + '\n'
    new_text = ast.unparse(ast.parse(new_path.read_text())) + '\n'
    if old_text.count('2 < a < d and a % 2') != 1:
        raise AssertionError('Unexpected control validator')
    if old_text.replace('2 < a < d and a % 2', 'a > 2 and a % 2') != new_text:
        raise AssertionError('The comparison is not exactly the specified validator change')

    old, new = source_functions(old_path), source_functions(new_path)
    manifest = json.loads((HERE / 'tests' / 'manifest.json').read_text())
    cases = []
    for item in manifest:
        data = (HERE / 'tests' / item['file']).read_bytes()
        if hashlib.sha256(data).hexdigest() != item['sha256']:
            raise AssertionError(('Fixture changed', item['name']))
        cases.append({'name': item['name'], 'raw': data.decode(), 'expected': item['expected']})

    # These goals pass the refined public shape/parity validator but fail the
    # old bound test, so they target precisely the removed check.
    bad_goals = {
        'free_root_slot': [3, 3],
        'far_root_slot': [999, 999],
        'at_Q_bound': [[5, 5]] * 3,
        'at_D_bound': [[7, 7]],
        'under_successor': [[7], [7]],
        'iterator_counter_escape': [[5, 0, 0], 0],
        'iterator_seed_escape': [[0, 5, 0], 0],
        'iterator_update_escape': [[0, 0, 5], 0],
        'nested_D_Q_bound': [[[9, 9]] * 3],
    }
    preflight = []
    for name, goal in bad_goals.items():
        if old['v'](goal) or not new['v'](goal):
            raise AssertionError(('Not a precise omitted-bound probe', name, goal))
        calls = []

        def forbidden_instruction():
            calls.append(1)
            raise RuntimeError('Proof data was consumed before rejecting the goal')

        new['q'] = forbidden_instruction
        try:
            new['c'](copy.deepcopy(goal))
        except TypeError:
            pass
        else:
            raise AssertionError(('Initial scope walk failed to reject', name))
        if calls:
            raise AssertionError(('Proof instruction was consumed', name))
        preflight.append({'name': name, 'refined_v_accepts': True, 'initial_c_rejects': 'TypeError', 'proof_instructions_consumed': 0})
        # Supply a known good-looking instruction, so rejection cannot be
        # attributed solely to an empty proof prefix.
        cases.append({'name': 'generated_' + name, 'raw': json.dumps([[0, 0, [0], 0], goal]), 'expected': False})

    valid = json.loads((HERE / 'tests' / 'native_computation.json').read_text())
    for label, prefix in [('null', None), ('boolean', True), ('float', 0.0), ('string', ''), ('object', {}), ('nested_boolean', [False])]:
        cases.append({'name': 'unused_' + label + '_prefix', 'raw': json.dumps([prefix] + valid), 'expected': False})
    for label, prefix in [('positive_integer', 123), ('negative_integer', -99), ('empty_list', [])]:
        cases.append({'name': 'unused_' + label + '_prefix', 'raw': json.dumps([prefix] + valid), 'expected': True})

    malformed = ['', '[', '[] trailing', '[1,]', '[+1]', '[01]', '{', 'null', 'true', '0.0', 'NaN', 'Infinity', '{}', '"[]"', '[]']
    for index, raw in enumerate(malformed):
        cases.append({'name': 'malformed_or_wrong_root_' + str(index), 'raw': raw, 'expected': False})
    for label, goal in [('negative', [-1, -1]), ('even', [4, 4]), ('reserved_one', [1, 1]), ('reserved_two', [2, 2]), ('noncanonical_Q', [[0, 0], [0, [0]], [0, 0]])]:
        cases.append({'name': 'retained_validation_' + label, 'raw': json.dumps([[0, 0, [0], 0], goal]), 'expected': False})

    jobs = [(case, program, optimized, None) for case in cases for program in ['control.py', 'checker.py'] for optimized in [False, True]]
    # Valid computation certificates of increasing term depth probe parser,
    # validator, scope-walk, and proof-kernel recursion failures. No arbitrary
    # deep certificate is declared accepted; equality of outcomes is required.
    resources = []
    for depth in [1, 10, 30, 80, 150, 300, 600]:
        numeral = '[' * depth + '0' + ']' * depth
        raw = '[[0,0,' + numeral + ',0],[[0,' + numeral + ',0],' + numeral + ']]'
        case = {'name': 'depth_' + str(depth), 'raw': raw}
        resources.append(case)
        jobs.extend((case, program, optimized, limit) for program in ['control.py', 'checker.py'] for optimized in [False, True] for limit in [100, 250, 1000])

    with ThreadPoolExecutor(max_workers=8) as pool:
        records = list(pool.map(invoke, jobs))

    for row in records:
        if row['expected'] is not None and row['accepted'] != row['expected']:
            raise AssertionError(('Unexpected standalone outcome', row))
    groups = {}
    for row in records:
        groups.setdefault((row['name'], row['optimized'], row['recursion_limit']), []).append(row)
    for key, rows in groups.items():
        if len(rows) != 2 or rows[0]['accepted'] != rows[1]['accepted']:
            raise AssertionError(('Old/new acceptance mismatch', key, rows))

    metrics = []
    for path, normalized in [(old_path, old_text), (new_path, new_text)]:
        data = normalized.encode()
        ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
        tokens = sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(normalized).readline))
        compressed = gzip.compress(data, compresslevel=9, mtime=0)
        (HERE / (path.name + '.normalized.gz')).write_bytes(compressed)
        metrics.append({'program': path.name, 'normalized_bytes': len(data), 'significant_tokens': tokens, 'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))), 'gzip9_bytes': len(compressed), 'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'normalized_sha256': hashlib.sha256(data).hexdigest()})

    result = {
        'status': 'passed', 'python': platform.python_version(),
        'change': 'Only remove the public validator upper slot bound a<d; first kernel scope walk retains it.',
        'same_kernel_and_other_code': True,
        'frozen_inherited_fixtures': len(manifest),
        'ordinary_test_inputs': len(cases), 'recursion_probe_shapes': len(resources),
        'subprocess_runs': len(records), 'normal_runs': sum(not x['optimized'] for x in records),
        'optimized_runs': sum(x['optimized'] for x in records),
        'acceptances': sum(x['accepted'] for x in records),
        'rejections': sum(not x['accepted'] for x in records),
        'recursion_error_runs': sum(x['recursion_error'] for x in records),
        'mismatches': 0, 'scope_preflight_probes': preflight, 'metrics': metrics,
        'boundary': 'Finite evidence supplements proof.txt. No universal proof-assistant theorem or preservation of exact error text, time, or memory use is claimed.',
        'records': records,
    }
    (HERE / 'validation.json').write_text(json.dumps(result, indent=2) + '\n')
    summary = {key: value for key, value in result.items() if key not in ['records', 'scope_preflight_probes']}
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
