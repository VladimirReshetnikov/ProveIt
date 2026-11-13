"""Reproduce whole-module metrics and acceptance/quotient-trace checks.

The instrumented programs are only test harnesses. All measured checkers
are standalone. Finite tests do not prove the inherited arithmetic bridge.
"""
import ast
import copy
import hashlib
import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
PROGRAMS = ('controls/checker240.py', 'code/token239.py', 'code/checker.py')
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
        tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}


def metric(name):
    raw = (ROOT / name).read_bytes()
    normalized = (ast.unparse(ast.parse(raw)) + '\n').encode()
    return {'file': name,
            'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(
                io.StringIO(normalized.decode()).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
            'normalized_bytes': len(normalized),
            'source_sha256': hashlib.sha256(raw).hexdigest(),
            'normalized_sha256': hashlib.sha256(normalized).hexdigest()}


def execute(name, payload, optimized):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(ROOT / name))
    try:
        run = subprocess.run(command, input=payload, capture_output=True, timeout=10)
        return {'accepted': run.returncode == 0 and run.stdout == b'ACCEPT\n',
                'exit_code': run.returncode,
                'exception': run.stderr.decode(errors='replace').splitlines()[-1]
                if run.stderr else ''}
    except subprocess.TimeoutExpired:
        return {'accepted': False, 'exit_code': None, 'exception': 'TIMEOUT'}


def instrument(name):
    tree = ast.parse((ROOT / name).read_text())
    tree.body = [s for s in tree.body
                 if isinstance(s, (ast.ImportFrom, ast.FunctionDef))
                 or isinstance(s, ast.Assign) and any(
                     isinstance(t, ast.Name) and t.id == 'k' for t in s.targets)]
    return compile(tree, name, 'exec')


def canonical(value):
    """The proof relation identifies generated False with integer zero."""
    if type(value) is bool:
        return int(value)
    if isinstance(value, (tuple, list, bytes)):
        return [canonical(v) for v in value]
    return value


def trace_run(compiled, records):
    packet_lines = [json.dumps(r, separators=(',', ':')) for r in records[1:]]
    cursor = 0
    digest = hashlib.sha256()
    calls = 0
    false_leaves_seen = 0

    def count_false(value):
        if type(value) is bool:
            return not value
        if isinstance(value, (tuple, list)):
            return sum(count_false(v) for v in value)
        return 0

    def read_line():
        nonlocal cursor
        if cursor == len(packet_lines):
            raise EOFError('no packet')
        line = packet_lines[cursor]
        cursor += 1
        return line

    namespace = {'input': read_line}
    exec(compiled, namespace)
    original = namespace['c']

    def tracked(*args):
        nonlocal calls, false_leaves_seen
        calls += 1
        false_leaves_seen += count_false(args)
        event = canonical([namespace['k'], args])
        digest.update(json.dumps(event, separators=(',', ':')).encode())
        value = original(*args)
        if value is not None:
            raise AssertionError('successful c returned a non-None value')
        return value

    namespace['c'] = tracked
    exception = ''
    try:
        tracked(bytes([0]), records[0])
        accepted = True
    except Exception as exc:
        accepted = False
        exception = type(exc).__name__
    return {'accepted': accepted, 'consumed': cursor,
            'floor': namespace['k'], 'calls': calls,
            'call_trace_sha256': digest.hexdigest(),
            'exception': exception, 'false_leaves_seen': false_leaves_seen}


def scalar_paths(value, prefix=()):
    if type(value) is int:
        yield prefix
    else:
        for j, child in enumerate(value):
            yield from scalar_paths(child, prefix + (j,))


def altered(records, rng, index):
    out = copy.deepcopy(records)
    mode = index % 4
    if len(out) < 2:
        return out
    if mode == 0:
        paths = list(scalar_paths(out[1:]))
        if paths:
            path = rng.choice(paths)
            parent = out
            translated = (path[0] + 1,) + path[1:]
            for j in translated[:-1]:
                parent = parent[j]
            old = parent[translated[-1]]
            parent[translated[-1]] = rng.choice([0, 1, -1, -2, 3, 5, old + 1, old - 1])
    elif mode == 1:
        out.pop(rng.randrange(1, len(out)))
    elif mode == 2:
        j = rng.randrange(1, len(out))
        out.insert(j, copy.deepcopy(out[j]))
    elif len(out) > 2:
        j, k = rng.sample(range(1, len(out)), 2)
        out[j], out[k] = out[k], out[j]
    return out


def structural_checks():
    control = (ROOT / 'controls/checker240.py').read_text()
    expected = control.replace('c(g, s) or k * bool(s or len(a) == 2)',
                               '(c(g, s) or s or len(a) == 2) and k')
    fused = (ROOT / 'code/token239.py').read_text()
    first = ast.dump(ast.parse(expected)) == ast.dump(ast.parse(fused))
    expected = fused.replace('k = 0\n', '').replace('d=0', 'd=(k := 0)').replace(
        's, u, t = r = loads(input())',
        'match loads(input()):\n        case [s,u,t] as r:\n            pass')
    second = ast.dump(ast.parse(expected)) == ast.dump(ast.parse(
        (ROOT / 'code/checker.py').read_text()))
    return {'fusion_is_only_first_change': first,
            'initialization_and_pattern_are_only_second_changes': second}


def main():
    fixtures = sorted((ROOT / 'fixtures').glob('*.jsonl'))
    tests = []
    for path in fixtures:
        expected = not path.name.startswith(('reject_', 'direct_false'))
        tests.append((path.name, path.read_bytes(), expected))
        if expected:
            lines = path.read_text().splitlines()
            bad = ('[0,[0]]\n' + '\n'.join(lines[1:]) + '\n').encode()
            tests.append((path.stem + '_false_goal', bad, False))
    for index, packet in enumerate([[], [0], [0, 0], [0, 0, 0, 0],
                                    0, -1, None, True, 'abc', {}]):
        tests.append(('malformed_packet_' + str(index),
                      ('[0,[0]]\n' + json.dumps(packet) + '\n').encode(), False))
    tests.append(('truncated_input', b'[0,[0]]\n', False))
    rows = []
    for name in (*PROGRAMS, 'code/readable.py'):
        for label, payload, expected in tests:
            for optimized in (False, True):
                rows.append({'program': name, 'fixture': label,
                             'expected': expected, 'optimized': optimized,
                             **execute(name, payload, optimized)})
    compiled = {name: instrument(name) for name in PROGRAMS}
    rng = random.Random(20261113)
    traces = []
    for path in fixtures:
        records = [json.loads(line) for line in path.read_text().splitlines()]
        for index in range(16):
            payload = records if index == 0 else altered(records, rng, index)
            result = {name: trace_run(code, payload) for name, code in compiled.items()}
            keys = ('accepted', 'consumed', 'floor', 'calls', 'call_trace_sha256')
            signatures = [tuple(row[k] for k in keys) for row in result.values()]
            traces.append({'fixture': path.name, 'mutation': index,
                           'equal_modulo_false_zero': all(x == signatures[0]
                                                         for x in signatures),
                           'results': result})
    failures = [r for r in rows if r['accepted'] != r['expected']
                or r['exception'] == 'TIMEOUT']
    trace_failures = [r for r in traces if not r['equal_modulo_false_zero']]
    structure = structural_checks()
    report = {'python': sys.version, 'metrics': [metric(n) for n in PROGRAMS],
              'structural_checks': structure, 'fixture_inputs': len(tests),
              'cli_executions': len(rows), 'cli_failures': failures, 'cli_results': rows,
              'typed_quotient_trace_cases': len(traces),
              'typed_quotient_trace_failures': trace_failures,
              'typed_quotient_trace_results': traces,
              'scope': 'Tests support the written universal source simulation; arithmetic correspondence inherited.'}
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'metrics': report['metrics'], 'structural_checks': structure,
                      'cli_executions': len(rows), 'cli_failures': len(failures),
                      'typed_quotient_trace_cases': len(traces),
                      'typed_quotient_trace_failures': len(trace_failures),
                      'maximum_false_leaf_count': max(r['results']['code/token239.py']['false_leaves_seen']
                                                      for r in traces)}, indent=2))
    if failures or trace_failures or not all(structure.values()):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
