"""Focused offline regression and source-comparison checks for two candidates."""
import ast
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'reference/control_tokens240.py'
FIXTURES = ROOT / 'fixtures'
PROGRAMS = [BASE, ROOT / 'code/checker_tokens239.py', ROOT / 'code/checker_ast257.py', ROOT / 'code/checker_readable.py']
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    source = ast.unparse(ast.parse(path.read_text())) + '\n'
    return {'file': str(path.relative_to(ROOT)),
            'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(source).readline)),
            'ast_nodes': len(list(ast.walk(ast.parse(source)))),
            'normalized_bytes': len(source.encode()),
            'sha256': hashlib.sha256(source.encode()).hexdigest()}


def run(path, data, optimized):
    argv = [sys.executable, '-I', '-S', '-B'] + (['-O'] if optimized else []) + [str(path)]
    result = subprocess.run(argv, input=data.encode(), capture_output=True, timeout=15)
    return {'accepted': result.returncode == 0 and result.stdout == b'ACCEPT\n',
            'exit_code': result.returncode}


def structural_check():
    source = BASE.read_text()
    changed = source.replace('c(g, s) or k * bool(s or len(a) == 2)',
                             'k if c(g, s) or s or len(a) == 2 else 0')
    assert changed != source
    assert ast.dump(ast.parse(changed)) == ast.dump(ast.parse(PROGRAMS[1].read_text()))
    changed = changed.replace('k = 0\n', '').replace('d=0):', 'd=(k := 0)):')
    changed = changed.replace('s, u, t = r = loads(input())',
                              'match loads(input()):\n        case [s, u, t] as r:\n            pass')
    assert ast.dump(ast.parse(changed)) == ast.dump(ast.parse(PROGRAMS[2].read_text()))
    return {'conditional_is_only_token_profile_change': True,
            'ast_profile_is_exact_three_change_composition': True}


def main():
    cases = []
    for path in sorted(FIXTURES.glob('*.jsonl')):
        data = path.read_text()
        positive = path.name != 'future_witness_before_major.jsonl'
        cases.append((path.name, data, positive))
        if positive:
            cases.append((path.stem + '_false_goal', '[0,[0]]\n' + '\n'.join(data.splitlines()[1:]) + '\n', False))
    for packet in [0, [], [0], [0, 0], [0, 0, 0, 0], 'abc', None, True]:
        cases.append(('malformed_packet_' + repr(packet), '0\n' + json.dumps(packet) + '\n', False))
    cases.append(('neutral_leaf', '0\n[0,0,0]\n', True))
    cases.append(('empty_stream', '', False))
    cases.append(('missing_packet', '[0,0]\n', False))
    rows = []
    for name, data, expected in cases:
        for program in PROGRAMS:
            for optimized in [False, True]:
                rows.append({'case': name, 'program': program.name, 'optimized': optimized,
                             'expected': expected, **run(program, data, optimized)})
    failures = [r for r in rows if r['accepted'] != r['expected']]
    boundary = []
    attack = (FIXTURES / 'future_witness_before_major.jsonl').read_text()
    for path in PROGRAMS:
        lines = iter(attack.splitlines())
        consumed = []
        def supplied_input():
            line = next(lines)
            consumed.append(line)
            return line
        try:
            exec(compile(path.read_text(), str(path), 'exec'),
                 {'input': supplied_input, 'print': lambda *args: None})
            exception = 'NONE'
        except Exception as exc:
            exception = type(exc).__name__
        boundary.append({'program': path.name, 'lines_consumed': len(consumed), 'exception': exception})
        if len(consumed) != 2 or exception != 'TypeError':
            failures.append({'scope_boundary_failed': path.name})
    receipt = {'python': sys.version, 'source_checks': structural_check(),
               'metrics': [measure(p) for p in PROGRAMS],
               'case_count': len(cases), 'executions': len(rows), 'failures': failures,
               'scope_boundary': boundary, 'results': rows,
               'limits': 'Finite regression checks do not replace the universal source-level proof or the inherited iPRA interpretation theorem.'}
    (ROOT / 'evidence/verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
