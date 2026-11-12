"""Reproduce translation checks and whole-module source measurements."""
import ast
import copy
import importlib.util
import io
import json
import subprocess
import sys
import tokenize
from pathlib import Path
from convert import convert, decode, control

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'reference/fixtures/positive'


def measure(path):
    source = ast.unparse(ast.parse(path.read_text())) + '\n'
    tokens = [t for t in tokenize.generate_tokens(io.StringIO(source).readline)
              if t.type not in (tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE,
                                tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
                                tokenize.ENDMARKER)]
    return {'tokens': len(tokens), 'ast_nodes': sum(1 for _ in ast.walk(ast.parse(source))),
            'bytes': len(source.encode())}


def main():
    cases = []
    for path in sorted(SOURCE.glob('*.json')):
        source = json.loads(path.read_text())
        data = convert(source)
        control.check(decode(data))
        if convert(decode(data)) != data:
            raise AssertionError(('stream round trip', path))
        target = ROOT / 'tests' / path.name
        target.write_text(json.dumps(data, separators=(',', ':')) + '\n')
        cases.append((path.stem, data, True))
    basic = [[0, 0], [0, 0]]
    cases += [
        ('false_goal', [[0, 0], [0, [0, 0, 0]]], False),
        ('goal_boolean_alias', [[0, 0], [False, False]], False),
        ('goal_float_alias', [[0, 0], [0.0, 0]], False),
        ('false_opcode', [[False, []], [0, 0]], False),
        ('float_opcode', [[0.0, 0], [0, 0]], False),
        ('unused_prefix', [[0, 0]] + basic, False),
        ('bad_arity', [[0, 0, 0], [0, 0]], False),
        ('free_term', [[0, -1], [-1, -1]], False),
        ('bad_erased_body', [[0, [0, 0, -1]], [[0, 0, -1], [0, 0, -1]]], False),
        ('close_extra_payload', [[[], 0], [[0, 0]]], False),
        ('negative_clause', [[-1, 0], [0, 0]], False),
        ('out_of_range_clause', [[1, 0], [0, 0]], False),
    ]
    receipt = []
    for name, data, expected in cases:
        for checker in ('two_fields.py', 'two_fields_compact.py'):
            for optimized in (False, True):
                cmd = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / 'code' / checker)]
                r = subprocess.run(cmd, input=json.dumps(data), text=True, capture_output=True)
                accepted = r.returncode == 0 and r.stdout == 'ACCEPT\n'
                if accepted != expected:
                    raise AssertionError((name, checker, optimized, expected, r.returncode, r.stdout, r.stderr))
                receipt.append({'name': name, 'checker': checker, 'optimized': optimized, 'accepted': accepted})
    for group, expected in (('positive', True), ('negative', False)):
        for path in sorted((ROOT / 'reference/fixtures' / group).glob('*.json')):
            for optimized in (False, True):
                cmd = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / 'code/tree_control.py')]
                r = subprocess.run(cmd, input=path.read_text(), text=True, capture_output=True)
                accepted = r.returncode == 0 and r.stdout == 'ACCEPT\n'
                if accepted != expected:
                    raise AssertionError((path, optimized, expected, r.returncode, r.stdout, r.stderr))
                receipt.append({'name': path.stem, 'checker': 'tree_control.py', 'optimized': optimized, 'accepted': accepted})
    result = {'python': sys.version, 'cases': len(cases), 'runs': len(receipt),
              'metrics': {str(p.relative_to(ROOT)): measure(p) for p in
                          (ROOT / 'reference/conditional_copy.py', ROOT / 'code/tree_control.py',
                           ROOT / 'code/two_fields.py', ROOT / 'code/two_fields_compact.py')},
              'results': receipt}
    (ROOT / 'evidence/verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'results'}, indent=2))


if __name__ == '__main__':
    main()
