"""Explicit inherited generic-opener JSON aliases, checked by complete CLIs."""
import copy
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


def main():
    saved = json.loads((ROOT / 'tests/cases.json').read_text())
    rows = []
    for checker in ('code/checker_tokens.py', 'code/checker_ast.py'):
        def arithmetic(seed):
            if checker == 'code/checker_ast.py':
                return [None, 0, seed, 0]
            return [0, [0, seed, 0], 0, 0]
        tests = []
        aliases = [('empty_string', '', True), ('empty_object', {}, True),
                   ('empty_key_object', {'': {'arbitrary_value': None}}, True),
                   ('nonempty_string', 'a', False),
                   ('nonempty_key_object', {'a': 0}, False),
                   ('mixed_keys_object', {'': 0, 'a': 0}, False)]
        for name, seed, accept in aliases:
            tests.append(dict(name='numeric_' + name, accept=accept,
                              packet=[arithmetic(seed), [[0, seed, 0], seed]]))
        for name, goal, accept in aliases:
            tests.append(dict(name='formula_' + name, accept=accept,
                              packet=[[[], 0, 0, [0]], goal]))
        # A used nonempty dictionary major is rejected by its mandatory
        # `m * 3` export, even if the generic opener gave it a harmless meaning.
        tests.append(dict(name='empty_key_dictionary_as_used_major', accept=False,
                          packet=[[[], 0, 0, [0]],
                                  [{'': 'value_is_ignored'}, None, None, 0], [[]]]))
        neutral = next(c for c in saved[checker]
                       if c['name'] == 'neutral_wrong_endpoints_then_valid_proof')
        packet = copy.deepcopy(neutral['packet'])
        # The outermost instruction is the neutral major packet.
        packet[-2][1] = {'a': ['never', 'traversed']}
        packet[-2][2] = {'': None}
        tests.append(dict(name='dictionaries_in_unused_endpoint_fields',
                          accept=True, packet=packet))
        for test in tests:
            for optimized in (False, True):
                result = subprocess.run([sys.executable] + (['-O'] if optimized else []) +
                                        [str(ROOT / checker)], input=json.dumps(test['packet']),
                                        text=True, capture_output=True, timeout=12)
                accepted = result.returncode == 0 and result.stdout.strip() == 'ACCEPT'
                rows.append(dict(checker=checker, name=test['name'], optimized=optimized,
                                 expected=test['accept'], accepted=accepted,
                                 passed=accepted == test['accept'],
                                 packet=test['packet'],
                                 diagnostic=result.stderr if accepted != test['accept'] else ''))
    output = dict(scope='Specific finite raw alias checks; fixed Python recursion limit.',
                  runs=len(rows), passed=sum(r['passed'] for r in rows), rows=rows)
    (ROOT / 'evidence/alias_results.json').write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({k: v for k, v in output.items() if k != 'rows'}))
    failures = [r for r in rows if not r['passed']]
    if failures:
        print(json.dumps(failures, indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
