"""Recompute whole-module sizes and replay the supplied regression suite.

This verification utility is not imported by either measured checker.
Finite tests supplement PROOF.txt; they do not establish the universal
soundness, completeness or interpretation theorems.
"""
import ast
import concurrent.futures
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize


ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
        tokenize.DEDENT, tokenize.ENDMARKER, tokenize.COMMENT}


def measure(name):
    raw = (ROOT / name).read_bytes()
    tree = ast.parse(raw)
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.body and isinstance(node.body[0], ast.Expr) and isinstance(node.body[0].value, ast.Constant) and isinstance(node.body[0].value.value, str):
                node.body.pop(0)
                if not node.body and not isinstance(node, ast.Module):
                    node.body.append(ast.Pass())
    normalized = (ast.unparse(tree) + '\n').encode()
    tokens = tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
    return {
        'file': name,
        'significant_tokens': sum(token.type not in SKIP for token in tokens),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_utf8_bytes': len(normalized),
        'normalized_gzip9_mtime0_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'raw_sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized).hexdigest(),
    }


def diagnostic_shift(tree):
    # Keep noncontract values for the inherited malformed-input regressions.
    if type(tree) is int:
        return tree + 2 if tree > 0 else tree
    if type(tree) is list:
        return [diagnostic_shift(child) for child in tree]
    return tree


def shifted_input(source):
    target = diagnostic_shift(source)
    for original, shifted in zip(source[:-1], target[:-1]):
        if type(original) is list and len(original) == 4 and original[0] == []:
            shifted[0] = 0
    return target


def run(job):
    case, name, optimized = job
    data = case['input'] if name == 'control469.py' else shifted_input(case['input'])
    data = (json.dumps(data, separators=(',', ':')) + '\n').encode()
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(ROOT / name))
    timeout = False
    try:
        result = subprocess.run(command, input=data, capture_output=True, timeout=12)
        accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
    except subprocess.TimeoutExpired:
        accepted, timeout = False, True
    return {'case': case['name'], 'kind': case['kind'], 'program': name,
            'optimized': optimized, 'expected': case['expected'],
            'accepted': accepted, 'timed_out': timeout,
            'passed': accepted == case['expected'] and not timeout,
            'input_sha256': hashlib.sha256(data).hexdigest()}


def main():
    control = (ROOT / 'control469.py').read_text()
    exact = control.replace('d=0:', 'd=2:').replace('d=3', 'd=5')
    exact = exact.replace('[s, u, t], 3)', '[s, u, t], 5)')
    exact = exact.replace('i(*a, t, 2)', 'i(*a, t, 4)')
    exact = exact.replace('c([[]], *q())', 'c([0], *q())')
    exact = ast.unparse(ast.parse(exact)) + '\n'
    exact_transformation = exact == (ROOT / 'compact468.py').read_text()
    cases = json.loads((ROOT / 'fixtures.json').read_text())
    jobs = [(case, name, optimized) for case in cases
            for name in ('control469.py', 'compact468.py')
            for optimized in (False, True)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        outcomes = list(pool.map(run, jobs))
    metrics = [measure(name) for name in ('control469.py', 'compact468.py',
                                          'reference_offset472.py', 'checker_readable.py')]
    receipt = {
        'python': sys.version,
        'metric_reference_python': 'CPython 3.12.14',
        'normalization': 'remove docstrings, then ast.unparse(whole AST) plus LF',
        'exact_transformation_passed': exact_transformation,
        'case_count': len(cases), 'process_executions': len(outcomes),
        'metrics': metrics,
        'failures': [row for row in outcomes if not row['passed']],
        'outcomes': outcomes,
        'proof_status': 'Written trace-translation proof in PROOF.txt; finite tests are supplementary.',
        'input_contract': 'Canonical closed guarded Eq/D public goal, initial floor zero, and finite exact integer/list data. Internal raw trees need not be canonical.',
        'diagnostic_limit': 'Malformed fixtures are retained as operational regressions; no universal arbitrary-raw recoding claim is made.',
    }
    (ROOT / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: receipt[key] for key in (
        'exact_transformation_passed', 'case_count', 'process_executions',
        'metrics', 'failures')}, indent=2))
    if receipt['failures'] or not exact_transformation:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
