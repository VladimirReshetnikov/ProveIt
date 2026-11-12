"""Compare the exact context-floor transformation on inherited certificates.

Finite tests are implementation checks, not a proof of mathematical soundness.
The separate invariant note supplies the exact simulation argument.
"""
import ast
from concurrent.futures import ThreadPoolExecutor
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent


def metrics(name):
    raw = (ROOT / name).read_bytes()
    tree = ast.parse(raw)
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and type(node.body[0].value.value) is str):
                node.body.pop(0)
    source = ast.unparse(tree) + '\n'
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
               tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT}
    return {'file': name,
            'significant_tokens': sum(t.type not in ignored for t in
                tokenize.generate_tokens(io.StringIO(source).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(source))),
            'normalized_bytes': len(source.encode()),
            'sha256': hashlib.sha256(raw).hexdigest()}


def exact_transform():
    source = (ROOT / 'baseline492.py').read_text()
    transformed = source.replace(
        'def c(g, a, k=0):', 'def c(g, a):\n    k = 1-len(g)')
    transformed = transformed.replace('c(g, m, k)', 'c(g, m)')
    transformed = transformed.replace('], [k]), k)', '], [k]))')
    return ast.dump(ast.parse(transformed)) == ast.dump(
        ast.parse((ROOT / 'context_floor.py').read_text()))


def run(job):
    case, checker, optimized = job
    payload = (ROOT / 'fixtures' / case['file']).read_bytes()
    if hashlib.sha256(payload).hexdigest() != case['sha256']:
        raise ValueError('Fixture hash mismatch: ' + case['file'])
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command += ['-O']
    command += [str(ROOT / checker)]
    try:
        result = subprocess.run(command, input=payload, capture_output=True,
                                timeout=5)
        accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
        return {'case': case['file'], 'checker': checker,
                'optimized': optimized, 'accepted': accepted,
                'expected': case['expected'], 'timeout': False}
    except subprocess.TimeoutExpired:
        return {'case': case['file'], 'checker': checker,
                'optimized': optimized, 'accepted': False,
                'expected': case['expected'], 'timeout': True}


def main():
    cases = json.loads((ROOT / 'fixtures/cases.json').read_text())
    programs = ['baseline492.py', 'context_floor.py', 'readable.py']
    jobs = [(case, checker, optimized) for case in cases
            for checker in programs for optimized in (False, True)]
    with ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run, jobs))
    lookup = {(r['case'], r['checker'], r['optimized']): r for r in results}
    discrepancies = []
    for case in cases:
        for optimized in (False, True):
            control = lookup[(case['file'], 'baseline492.py', optimized)]
            for checker in programs:
                row = lookup[(case['file'], checker, optimized)]
                row['same_as_control'] = row['accepted'] == control['accepted']
                row['matches_known_expectation'] = (case['expected'] is None or
                    row['accepted'] == case['expected'])
                if (not row['same_as_control'] or
                        not row['matches_known_expectation'] or row['timeout']):
                    discrepancies.append(row)
    # Diagnostic only: no success or soundness claim for this naive variant.
    diagnostic_cases = [case for case in cases if
        any(name in case['file'] for name in
            ('future_scope_attack', 'phase_guard_counterexample',
             'future_witness_capture', 'context_leak_attack'))]
    diagnostic = [run((case, 'experiments/unsound_inclusive_floor.py', False))
                  for case in diagnostic_cases]
    report = {'python': platform.python_version(),
              'upstream_commit': '36d37fc1071fe289371f6bcd7dcfa0eac593a5a6',
              'exact_source_transform_verified': exact_transform(),
              'metrics': [metrics(name) for name in programs],
              'unique_fixtures': len(cases), 'cli_runs': len(results),
              'discrepancies': discrepancies,
              'results': results, 'naive_experiment': diagnostic,
              'limitations': [
                  'No new mathematical axiom or inference rule is proposed.',
                  'The size target is not met: the compact variant grows.',
                  'The inherited public syntax contract is unchanged.',
                  'No Lean or Rocq verification of Python is claimed.',
                  'All comparison runs are finite regression checks.',
                  'The diagnostic variant has no correctness claim.']}
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: report[key] for key in
        ('python', 'exact_source_transform_verified', 'metrics',
         'unique_fixtures', 'cli_runs', 'discrepancies', 'naive_experiment')},
        indent=2))
    if discrepancies or not report['exact_source_transform_verified']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
