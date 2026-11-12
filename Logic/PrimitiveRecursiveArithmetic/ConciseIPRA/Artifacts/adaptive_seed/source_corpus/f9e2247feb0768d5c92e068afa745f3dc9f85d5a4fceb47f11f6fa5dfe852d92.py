"""Portable finite validation of complete Choice-DI and scalar-SC kernels.

This is untrusted supporting code. It is not imported by any proof checker.
The written soundness and interpretation proofs establish the general claims.
"""
import ast
import copy
import importlib.util
import json
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('source_measure', ROOT / 'code/source_measure.py')
measure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(measure)


def core(path):
    tree = ast.parse(path.read_text())
    tree.body = [n for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom, ast.FunctionDef, ast.Assign))]
    return compile(ast.fix_missing_locations(tree), str(path), 'exec')


def run(code, packet, unit=False):
    namespace = {}
    exec(code, namespace)
    data = copy.deepcopy(packet)
    try:
        namespace['q'] = data.pop
        result = namespace['c'](data.pop(), [])
        accepted = True if unit else bool(result)
    except BaseException:
        accepted = False
    return accepted, namespace['k'], len(data) if isinstance(data, list) else None


def validate_program(relative, cases, unit=False):
    path = ROOT / relative
    code = core(path)
    failures = []
    for case in cases:
        result = run(code, case['packet'], unit)
        if result[0] != case['accept']:
            failures.append({'case': case['name'], 'actual': result[0], 'expected': case['accept']})
    cli_failures = []
    for case in cases:
        for optimized in (False, True):
            command = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
            process = subprocess.run(command, input=json.dumps(case['packet']), text=True,
                                     capture_output=True, timeout=10)
            expected = 'ACCEPT\n' if case['accept'] else 'REJECT\n'
            if process.stdout != expected or (process.returncode == 0) != case['accept']:
                cli_failures.append({'case': case['name'], 'optimized': optimized,
                                     'stdout': process.stdout, 'exit_status': process.returncode})
    return {'file': relative, 'metrics': measure.metrics(path),
            'in_process_cases': len(cases), 'in_process_failures': failures,
            'cli_runs': 2 * len(cases), 'cli_failures': cli_failures}


def main():
    choice = json.loads((ROOT / 'fixtures/choice_cases.json').read_text())['cases']
    sc = json.loads((ROOT / 'fixtures/scalar_sc_cases.json').read_text())['cases']
    programs = [validate_program('code/choice_checker.py', choice),
                validate_program('code/choice_tokens.py', choice),
                validate_program('code/choice_structure.py', choice, unit=True),
                validate_program('code/scalar_sc_checker.py', sc)]
    old = core(ROOT / 'comparison/old_byte_min.py')
    new = core(ROOT / 'code/choice_checker.py')
    heads = [None, False, True, 0, 1, -1, 0.0, 0.5, 1.0, '', 'x', {}, {'x': 0},
             [], [0], [0, 0], [0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0, 0],
             [None], [[0]], [[-1]], [[0, 0]], [0, []], [[], 0]]
    mutation_count = accepted_count = 0
    differences = []
    for case in choice[:45]:
        for index, cell in enumerate(case['packet'][:-1]):
            if index >= 16:
                break
            if not isinstance(cell, list) or len(cell) != 2:
                continue
            for head in heads:
                packet = copy.deepcopy(case['packet'])
                packet[index][0] = copy.deepcopy(head)
                before, after = run(old, packet), run(new, packet)
                mutation_count += 1
                accepted_count += int(before[0])
                if before[0] != after[0] or (before[0] and before != after):
                    differences.append({'case': case['name'], 'instruction': index,
                                        'head': head, 'before': before, 'after': after})
    report = {'python': platform.python_version(), 'programs': programs,
              'choice_cases': len(choice), 'sc_cases': len(sc),
              'sc_positive_cases': sum(c['accept'] for c in sc),
              'sc_negative_cases': sum(not c['accept'] for c in sc),
              'in_process_total': sum(p['in_process_cases'] for p in programs),
              'cli_total': sum(p['cli_runs'] for p in programs),
              'dispatch_mutations': mutation_count, 'accepted_mutations': accepted_count,
              'differential_failures': differences,
              'all_passed': not differences and all(not p['in_process_failures'] and
                                                    not p['cli_failures'] for p in programs),
              'scope': 'Finite canonical derivations and targeted boundary checks. The nonconstant SC example is a closed proof containing a contextual SC application, not an unconditional false equation. These tests do not formalize the metatheory.'}
    (ROOT / 'evidence/kernel_validation.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    if not report['all_passed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
