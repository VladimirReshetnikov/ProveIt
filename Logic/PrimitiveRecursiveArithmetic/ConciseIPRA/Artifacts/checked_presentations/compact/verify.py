"""Reproduce metrics and matched tests; all proof checkers remain standalone.

Finite tests support the source-transformation proof in proof.txt. They do not
constitute a new proof of arithmetic soundness or of bi-interpretability.
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
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
        tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}


def metric(path):
    raw = path.read_bytes()
    normalized = (ast.unparse(ast.parse(raw)) + '\n').encode()
    return {
        'file': str(path.relative_to(ROOT)),
        'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(
            io.StringIO(normalized.decode()).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
        'normalized_bytes': len(normalized),
        'source_sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized).hexdigest(),
    }


def execute(program, payload, optimized):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(ROOT / program))
    try:
        run = subprocess.run(command, input=payload, capture_output=True, timeout=10)
        return {
            'accepted': run.returncode == 0 and run.stdout == b'ACCEPT\n',
            'exit_code': run.returncode,
            'exception': run.stderr.decode(errors='replace').splitlines()[-1]
            if run.stderr else '',
        }
    except subprocess.TimeoutExpired:
        return {'accepted': False, 'exit_code': None, 'exception': 'TIMEOUT'}


def instrument(path):
    tree = ast.parse(path.read_text())
    tree.body = [s for s in tree.body
                 if isinstance(s, (ast.ImportFrom, ast.FunctionDef))
                 or isinstance(s, ast.Assign) and any(
                     isinstance(t, ast.Name) and t.id == 'k' for t in s.targets)]
    return compile(tree, str(path), 'exec')


def trace_run(compiled, records):
    """Execute definitions against the same decoded integer/list records.

    Record calls, consumed packets and final floor. The wrapper is untrusted
    test instrumentation; it is absent from every measured checker.
    """
    packet_lines = [json.dumps(r, separators=(',', ':')) for r in records[1:]]
    cursor = 0
    digest = hashlib.sha256()
    calls = 0

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
        nonlocal calls
        calls += 1
        digest.update(json.dumps([namespace['k'], args], separators=(',', ':')).encode())
        value = original(*args)
        if value is not None:
            raise AssertionError('a successful call returned a non-None value')
        return value

    namespace['c'] = tracked
    exception = ''
    try:
        tracked(records[0])
        accepted = True
    except Exception as exc:
        accepted = False
        exception = type(exc).__name__
    return {'accepted': accepted, 'exception': exception, 'consumed': cursor,
            'floor': namespace['k'], 'calls': calls, 'call_trace_sha256': digest.hexdigest()}


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


def main():
    programs = [('lines', 'controls/checker242.py'),
                ('lines', 'code/checker240.py'),
                ('whole', 'controls/checker247_whole.py'),
                ('whole', 'code/checker245_whole.py')]
    metrics = [metric(ROOT / program) for _, program in programs]
    rows = []
    for framing, program in programs:
        for path in sorted((ROOT / 'fixtures' / framing).glob('*')):
            expected = not path.name.startswith('reject_') and not path.name.startswith('direct_false')
            for optimized in (False, True):
                rows.append({'program': program, 'fixture': path.name,
                             'kind': 'inherited', 'expected': expected,
                             'optimized': optimized,
                             **execute(program, path.read_bytes(), optimized)})
            if expected:
                if framing == 'lines':
                    lines = path.read_text().splitlines()
                    bad = ('[0,[0]]\n' + '\n'.join(lines[1:]) + '\n').encode()
                else:
                    data = json.loads(path.read_text())
                    data[-1] = [0, [0]]
                    bad = json.dumps(data).encode()
                for optimized in (False, True):
                    rows.append({'program': program, 'fixture': path.name,
                                 'kind': 'false_public_goal', 'expected': False,
                                 'optimized': optimized,
                                 **execute(program, bad, optimized)})
    control = instrument(ROOT / 'controls/checker242.py')
    candidate = instrument(ROOT / 'code/checker240.py')
    rng = random.Random(20261112)
    traces = []
    for path in sorted((ROOT / 'fixtures' / 'lines').glob('*.jsonl')):
        records = [json.loads(line) for line in path.read_text().splitlines()]
        for index in range(32):
            payload = records if index == 0 else altered(records, rng, index)
            old = trace_run(control, payload)
            new = trace_run(candidate, payload)
            traces.append({'fixture': path.name, 'mutation': index,
                           'records_sha256': hashlib.sha256(json.dumps(payload).encode()).hexdigest(),
                           'equal': old == new, 'control': old, 'candidate': new})
    failures = [r for r in rows if r['accepted'] != r['expected'] or r['exception'] == 'TIMEOUT']
    trace_failures = [r for r in traces if not r['equal']]
    report = {'python': sys.version, 'metrics': metrics,
              'cli_executions': len(rows), 'cli_failures': failures, 'cli_results': rows,
              'typed_trace_cases': len(traces), 'typed_trace_failures': trace_failures,
              'typed_trace_results': traces,
              'scope': 'Finite tests plus written source correspondence; no new formal verification.'}
    (ROOT / 'evidence' / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'metrics': metrics, 'cli_executions': len(rows),
                      'cli_failures': len(failures), 'typed_trace_cases': len(traces),
                      'typed_trace_failures': len(trace_failures)}, indent=2))
    if failures or trace_failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
