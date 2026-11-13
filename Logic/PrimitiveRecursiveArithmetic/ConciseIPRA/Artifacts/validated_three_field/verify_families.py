"""Validate the independent AST and byte profiles against their own controls.

The fixtures use two different certificate protocols. The AST profile consumes
the old hypothesis-supply format; the byte profile uses shared computation
terminals and rotated packets. This runner deliberately keeps them separate.
Tests supplement the written correctness arguments; they do not prove them.
"""
from pathlib import Path
import ast
import concurrent.futures
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
           tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def metrics(path):
    tree = ast.parse(path.read_text())
    normalized = ast.unparse(tree) + '\n'
    return {
        'significant_tokens': sum(t.type not in IGNORED for t in
                                  tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': len(list(ast.walk(tree))),
        'normalized_utf8_bytes': len(normalized.encode()),
        'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized.encode()).hexdigest(),
    }


def rotate(document):
    """Convert only top-level [m,s,u,t] packets to [s,u,t,m]."""
    return [(r[1:] + r[:1] if isinstance(r, list) and len(r) == 4 else r)
            for r in document[:-1]] + document[-1:]


def source_audits():
    baseline = (ROOT / 'controls/checker_strict_ast356.py').read_text()
    expected = baseline.replace('t=c, d=0', 't=0j, d=0')
    old = "        g += b'\\x00'\n        m, s, u, t = q()"
    new = ("        match q():\n"
           "            case [m, s, u, t]:\n"
           "                g += b'\\x00'")
    if expected.count(old) != 1:
        raise AssertionError('AST control no longer has the frozen packet block')
    expected = expected.replace(old, new)
    expected = expected.replace('s and [s, u] or [t] * 3',
                                '([s, u] if s else [t] * 3)')
    if ast.dump(ast.parse(expected)) != ast.dump(ast.parse(
            (ROOT / 'code/checker_ast348.py').read_text())):
        raise AssertionError('AST profile differs beyond its three stated rewrites')

    baseline = (ROOT / 'controls/checker_strict597.py').read_text()
    old = '[[s and [s] or 1, u, t], i(t, r[:3], 3) if s else u]'
    new = 'i([[s and [s], u, t], i(t, r[:3], 3) if s else u])'
    if baseline.count(old) != 1:
        raise AssertionError('Byte control no longer has the frozen candidate')
    expected = baseline.replace(old, new)
    if ast.dump(ast.parse(expected)) != ast.dump(ast.parse(
            (ROOT / 'code/checker_bytes595.py').read_text())):
        raise AssertionError('Byte profile differs beyond normalized computation terminal')
    return {
        'ast348': 'Exact three-rewrite AST reconstruction passed',
        'bytes595': 'Exact single-rewrite AST reconstruction passed; theorem-set equivalence only',
    }


def run(job):
    family, case, checker, optimized = job
    document = case['certificate']
    if family == 'terminal':
        document = rotate(document)
    result = subprocess.run(
        [sys.executable, *(['-O'] if optimized else []), str(ROOT / checker)],
        input=json.dumps(document), text=True, capture_output=True, timeout=20)
    accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
    return {'family': family, 'case': case['name'], 'checker': checker,
            'optimized': optimized, 'expected': case['expected'],
            'accepted': accepted, 'exit_code': result.returncode}


def main():
    audits = source_audits()
    configurations = [
        ('supply', 'fixtures/supply_cases.json',
         ('controls/checker_strict_ast356.py', 'code/checker_ast348.py')),
        ('terminal', 'fixtures/terminal_cases.json',
         ('controls/checker_strict597.py', 'code/checker_bytes595.py')),
    ]
    jobs = []
    family_counts = {}
    measured = {}
    for family, fixture_path, checkers in configurations:
        cases = json.loads((ROOT / fixture_path).read_text())['cases']
        family_counts[family] = len(cases)
        for checker in checkers:
            measured[checker] = metrics(ROOT / checker)
        jobs.extend((family, case, checker, optimized) for case in cases
                    for checker in checkers for optimized in (False, True))
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
        results = list(executor.map(run, jobs))
    failures = [r for r in results if r['accepted'] != r['expected']]
    receipt = {'python': sys.version, 'source_audits': audits,
               'family_case_counts': family_counts, 'process_executions': len(results),
               'measurements': measured, 'failures': failures, 'results': results}
    output = ROOT / 'evidence/family_validation.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
