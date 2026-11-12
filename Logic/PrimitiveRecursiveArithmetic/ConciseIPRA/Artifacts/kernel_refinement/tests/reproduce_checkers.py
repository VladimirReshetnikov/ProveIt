"""Reproduce source measurements, certificate translation, and process checks.

This script and its frozen comparison files are untrusted support material.
No checker imports this script or a proof generator.
"""
import ast
import csv
import gzip
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
           tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
           tokenize.ENDMARKER}


class StripDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body = node.body[1:]
        return node

    visit_Module = visit_FunctionDef = visit_AsyncFunctionDef = visit_ClassDef = clean


def measure(path):
    raw = path.read_bytes()
    tree = ast.fix_missing_locations(StripDocstrings().visit(ast.parse(raw)))
    normalized = (ast.unparse(tree) + '\n').encode()
    compressed = gzip.compress(normalized, compresslevel=9, mtime=0)
    return {
        'path': str(path.relative_to(ROOT)),
        'sha256': hashlib.sha256(raw).hexdigest(),
        'raw_bytes': len(raw),
        'normalized_bytes': len(normalized),
        'significant_tokens': sum(t.type not in IGNORED for t in
            tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'gzip9_raw_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
        'gzip9_normalized_bytes': len(compressed),
    }, compressed


def translate_local(data):
    """Change only the administrative neutral major of four-field packets."""
    data = json.loads(json.dumps(data))
    if type(data) is list:
        for row in data[:-1]:
            if type(row) is list and len(row) == 4 and row[0] == []:
                row[0] = 0
    return data


def run_checker(checker, payload, optimized):
    command = [sys.executable]
    if optimized:
        command.append('-O')
    command.append(str(checker))
    process = subprocess.run(command, input=payload, capture_output=True,
                             timeout=20)
    return process.returncode == 0 and process.stdout == b'ACCEPT\n'


def reproduce():
    evidence = ROOT / 'evidence'
    evidence.mkdir(exist_ok=True)
    provenance = json.loads((evidence / 'checker_provenance.json').read_text())
    for item in provenance['files']:
        raw = (ROOT / item['path']).read_bytes()
        if hashlib.sha256(raw).hexdigest() != item['sha256']:
            raise ValueError('Frozen comparison changed: ' + item['path'])

    # Verify rather than silently overwrite the packaged transformed inputs.
    for original in sorted((ROOT / 'reference/certificates').glob('*.json')):
        source = json.loads(original.read_bytes())
        expected = translate_local(source) if original.stem.endswith('_local') else source
        actual = json.loads((ROOT / 'tests/certificates' / original.name).read_bytes())
        if actual != expected:
            raise ValueError('Incorrect packet translation: ' + original.name)

    declarations = json.loads((ROOT / 'reference/guarded_source_validation.json').read_text())
    expected_source = {(r['checker'], r['case'], r['optimized']): r['expected']
                       for r in declarations['receipts']}
    profiles = [
        ('checker_bytes.py', 'checker_bytes.py', 'local'),
        ('checker_ast.py', 'checker_ast.py', 'local'),
        ('checker_tokens.py', 'checker_tokens.py', 'global'),
        ('checker_strict.py', 'checker_strict.py', 'local'),
        ('readable_checker.py', 'checker_bytes.py', 'local'),
    ]
    receipts = []
    for candidate, control, kind in profiles:
        prior_name = ('exactroot_strict_checker.py' if control == 'checker_strict.py'
                      else 'exactroot_' + control)
        for original in sorted((ROOT / 'reference/certificates').glob('*_' + kind + '.json')):
            translated = ROOT / 'tests/certificates' / original.name
            for optimized in (False, True):
                reference = run_checker(ROOT / 'reference/checkers' /
                    ('guarded_source_' + control), original.read_bytes(), optimized)
                declared = expected_source.get((prior_name, original.name, optimized))
                if declared is not None and reference != declared:
                    raise ValueError('Frozen reference failed its declared verdict')
                accepted = run_checker(ROOT / 'code' / candidate,
                                       translated.read_bytes(), optimized)
                item = {'checker': candidate, 'case': original.name,
                        'optimized': optimized, 'expected': reference,
                        'accepted': accepted,
                        'matches_upstream_declared_case': declared is not None}
                receipts.append(item)
                if accepted != reference:
                    raise ValueError('Verdict mismatch: ' + json.dumps(item))

    metrics = []
    gzip_dir = evidence / 'normalized_gzip9'
    gzip_dir.mkdir(exist_ok=True)
    for path in sorted((ROOT / 'code').glob('*.py')):
        row, compressed = measure(path)
        metrics.append(row)
        (gzip_dir / (path.name + '.gz')).write_bytes(compressed)
    controls = [measure(p)[0] for p in sorted((ROOT / 'reference/checkers').glob('*.py'))]
    keys = ('significant_tokens', 'ast_nodes', 'normalized_bytes')
    compact = [r for r in metrics if Path(r['path']).name in
               {'checker_bytes.py', 'checker_ast.py', 'checker_tokens.py'}]
    results = {
        'python': platform.python_version(), 'zlib': zlib.ZLIB_RUNTIME_VERSION,
        'normalization': 'Remove only docstrings; ast.unparse; one final newline.',
        'gzip': 'compresslevel=9, mtime=0; full wrapper included; informational.',
        'selected': metrics, 'frozen_controls': controls,
        'compact_envelope': {k: min(r[k] for r in compact) for k in keys},
    }
    (evidence / 'checker_metrics.json').write_text(json.dumps(results, indent=2) + '\n')
    with (evidence / 'checker_metrics.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(metrics[0]))
        writer.writeheader()
        writer.writerows(metrics + controls)
    validation = {
        'comparisons': len(receipts), 'process_executions': 2 * len(receipts),
        'expected_acceptances': sum(r['expected'] for r in receipts),
        'expected_rejections': sum(not r['expected'] for r in receipts),
        'mismatches': [], 'receipts': receipts,
        'limits': 'Finite implementation checks; not a mechanized metatheorem.',
    }
    (evidence / 'checker_validation.json').write_text(json.dumps(validation, indent=2) + '\n')
    print(json.dumps({'compact_envelope': results['compact_envelope'],
                      'comparisons': len(receipts), 'mismatches': 0}))


if __name__ == '__main__':
    reproduce()
