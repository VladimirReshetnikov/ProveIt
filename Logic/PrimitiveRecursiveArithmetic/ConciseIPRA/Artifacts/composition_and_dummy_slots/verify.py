"""Reproduce finite tests of the eager-opening compositions.

The written semantic proof establishes soundness and canonical completeness.
These tests only validate the displayed implementations and regression cases.
"""
from pathlib import Path
import ast
import concurrent.futures
import copy
import gzip
import hashlib
import io
import json
import subprocess
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent
PROFILES = {
    'checker_tokens304.py': 'control_tokens306.py',
    'checker_joint311.py': 'control_joint313.py',
    'checker_ast345.py': 'control_ast348.py',
    'checker_bytes587.py': 'control_bytes589.py',
}
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
           tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    tree = ast.parse(path.read_text())
    normalized = (ast.unparse(tree) + '\n').encode()
    return {
        'tokens': sum(t.type not in IGNORED for t in
                      tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_bytes': len(normalized),
        'gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
    }


def source_audits():
    rows = []
    for candidate, control in PROFILES.items():
        source = (ROOT / 'controls' / control).read_text()
        if candidate == 'checker_bytes587.py':
            old = '[[s and [s] or 1, u, t], i(t, r[:3], 3) if s else u]'
            new = 'i([[s and [s], u, t], i(t, r[:3], 3) if s else u])'
            if source.count(old) != 1:
                raise ValueError('Frozen terminal control changed')
            source = source.replace(old, new)
        else:
            old = '(d % 2 or not g) and i(t, d=3)'
            new = 'd % 2 * i(t, d=3)'
            if source.count(old) != 1 or source.count("g += b'\\x00'") != 1:
                raise ValueError('Frozen eager control changed')
            source = source.replace(old, new).replace("g += b'\\x00'", 'g += [[]]')
        if ast.dump(ast.parse(source)) != ast.dump(ast.parse(
                (ROOT / 'code' / candidate).read_text())):
            raise ValueError('Unexpected source change: ' + candidate)
        rows.append({'candidate': candidate, 'control': control,
                     'exact_stated_source_transform': True})
    return rows


def translate_three(document):
    """Canonical compiler recoding, not a translator of arbitrary raw proofs.

    Canonical case/progress records have source 0 and false mode. The
    numerical specialization target uses zero code 1 and is kept unchanged.
    Applying this recoding to malformed tests is only a perturbation test.
    """
    document = copy.deepcopy(document)
    if type(document) is not list:
        return document
    for row in document[:-1]:
        if (type(row) is list and len(row) == 3 and
                type(row[0]) is int and row[0] == 0 and not row[1]):
            row[0] = []
    return document


def translate_four(document):
    """Replace the false major marker, leaving all numerical data intact."""
    document = copy.deepcopy(document)
    if type(document) is not list:
        return document
    for row in document[:-1]:
        if (type(row) is list and len(row) == 4 and
                type(row[0]) is int and row[0] == 0):
            row[0] = []
    return document


def translate_terminal(document):
    document = translate_four(document)
    return [(row[1:] + row[:1] if type(row) is list and len(row) == 4 else row)
            for row in document[:-1]] + document[-1:]


def run(job):
    name, checker, optimized, certificate, expected = job
    try:
        result = subprocess.run(
            [sys.executable, *(['-O'] if optimized else []),
             str(ROOT / 'code' / checker)], input=json.dumps(certificate),
            text=True, capture_output=True, timeout=15)
        accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
        error = result.stderr.splitlines()[-1] if result.stderr else None
    except subprocess.TimeoutExpired:
        accepted, error = False, 'timeout'
    return {'case': name, 'checker': checker, 'optimized': optimized,
            'expected': expected, 'accepted': accepted, 'error': error}


def main():
    audits = source_audits()
    jobs = []
    groups = [
        ('three_field', ('checker_tokens304.py', 'checker_joint311.py'), translate_three),
        ('supply', ('checker_ast345.py',), translate_four),
        ('terminal', ('checker_bytes587.py',), translate_terminal),
    ]
    counts = {}
    for family, checkers, translate in groups:
        cases = json.loads((ROOT / 'fixtures' / (family + '_cases.json')).read_text())['cases']
        counts[family] = {'cases': len(cases),
                          'positive_cases': sum(row['expected'] for row in cases)}
        for case in cases:
            certificate = translate(case['certificate'])
            for checker in checkers:
                for optimized in (False, True):
                    jobs.append((case['name'], checker, optimized, certificate, case['expected']))
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(run, jobs))
    failures = [row for row in results if row['accepted'] != row['expected']]
    metrics = {str(path.relative_to(ROOT)): measure(path)
               for folder in ('code', 'controls') for path in (ROOT / folder).glob('*.py')}
    receipt = {'python': sys.version, 'zlib_runtime': zlib.ZLIB_RUNTIME_VERSION,
               'gzip_settings': {'compresslevel': 9, 'mtime': 0},
               'scope': 'Finite verification; not a universal proof',
               'counts': counts, 'executions': len(results), 'failures': failures,
               'source_audits': audits, 'metrics': metrics, 'results': results}
    (ROOT / 'evidence' / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: value for key, value in receipt.items()
                      if key != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
