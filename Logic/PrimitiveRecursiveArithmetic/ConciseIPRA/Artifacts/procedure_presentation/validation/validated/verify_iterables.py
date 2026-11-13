"""Check the list-context invariant and neutral-byte iterable refinements."""
import ast
import concurrent.futures
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PAIRS = [('tokens', 'scope_strict_tokens.py', 'checker_strict_tokens_iterable.py'),
         ('ast', 'scope_strict_ast.py', 'checker_strict_ast_iterable.py')]


def run(job):
    checker, fixture, expected, optimized = job
    process = subprocess.run([sys.executable, *(['-O'] if optimized else []), str(checker)],
                             input=fixture.read_bytes(), capture_output=True, timeout=15)
    actual = process.returncode == 0 and process.stdout == b'ACCEPT\n'
    return dict(checker=str(checker.relative_to(ROOT)),
                fixture=str(fixture.relative_to(ROOT)), expected=expected,
                actual=actual, optimized=optimized)


def kernel(path):
    tree = ast.parse(path.read_text())
    tree.body = [node for node in tree.body if isinstance(node, ast.FunctionDef)]
    namespace = {}
    exec(compile(tree, str(path), 'exec'), namespace)
    return namespace


def trace(namespace, data):
    stack = copy.deepcopy(data)
    goal = stack.pop()
    calls, packets = [], []
    function = namespace['c']

    def packet():
        value = stack.pop()
        packets.append(copy.deepcopy(value))
        return value

    def profile(frame, event, _):
        if event == 'call' and frame.f_code is function.__code__:
            state = [frame.f_locals[key] for key in ('g', 'a', 'k')]
            if type(state[0]) is not list:
                raise AssertionError('The context ceased to be a list')
            calls.append(hashlib.sha256(repr(state).encode()).hexdigest())

    namespace['q'] = packet
    try:
        sys.setprofile(profile)
        function([], goal)
        outcome = 'returned'
    except BaseException as error:
        outcome = type(error).__name__
    finally:
        sys.setprofile(None)
    return outcome, calls, packets, stack


def main():
    positives = sorted((ROOT / 'scope_fixtures/odd').glob('*.json'))
    negatives = sorted((ROOT / 'scope_fixtures/negative').glob('*.json'))
    jobs = [(ROOT / folder / name, fixture, expected, optimized)
            for _, control, candidate in PAIRS
            for folder, name in [('controls', control), ('code', candidate)]
            for expected, fixtures in [(True, positives), (False, negatives)]
            for fixture in fixtures for optimized in (False, True)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(run, jobs))
    traces = []
    for category, control, candidate in PAIRS:
        left = kernel(ROOT / 'controls' / control)
        right = kernel(ROOT / 'code' / candidate)
        for fixture in positives + negatives:
            data = json.loads(fixture.read_text())
            a, b = trace(left, data), trace(right, data)
            traces.append(dict(category=category, fixture=fixture.name,
                               equal=a == b, calls=len(a[1]), packets=len(a[2])))
    summary = dict(python=sys.version, executions=len(results),
                   unexpected=[r for r in results if r['actual'] != r['expected']],
                   trace_comparisons=len(traces),
                   trace_mismatches=[r for r in traces if not r['equal']],
                   results=results, traces=traces)
    (ROOT / 'iterable_verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k not in ('results', 'traces')}, indent=2))
    if summary['unexpected'] or summary['trace_mismatches']:
        raise SystemExit('Iterable refinement verification failed')


if __name__ == '__main__':
    main()
