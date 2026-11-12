"""Standalone, standard-library verification of complete checker processes.

The proof checkers never import this runner or the stored proof trees. Only the
serialized certificate packet is supplied to their public standard-input API.
"""
import argparse
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent
PROFILES = ('baseline_529', 'qprogress_guarded', 'qprogress_extended')


def remove_docstrings(tree):
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef,
                             ast.AsyncFunctionDef)):
            body = node.body
            if (body and isinstance(body[0], ast.Expr)
                    and isinstance(body[0].value, ast.Constant)
                    and isinstance(body[0].value.value, str)):
                del body[0]
    return tree


def measure(path):
    source = path.read_bytes()
    tree = remove_docstrings(ast.parse(source.decode('utf-8')))
    normalized = (ast.unparse(tree) + '\n').encode('utf-8')
    ignored = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
               tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
               tokenize.ENDMARKER}
    tokens = sum(t.type not in ignored for t in tokenize.generate_tokens(
        io.StringIO(normalized.decode('utf-8')).readline))
    return {
        'file': str(path.relative_to(ROOT)),
        'sha256': hashlib.sha256(source).hexdigest(),
        'raw_bytes': len(source),
        'normalized_bytes': len(normalized),
        'significant_tokens': tokens,
        'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
        'raw_gzip_9_bytes': len(gzip.compress(source, compresslevel=9, mtime=0)),
        'normalized_gzip_9_bytes': len(gzip.compress(normalized, compresslevel=9,
                                                   mtime=0)),
    }


def run_case(profile, case, optimized):
    path = ROOT / 'code' / (profile + '.py')
    payload = case['raw'] if 'raw' in case else json.dumps(case['packet'])
    command = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
    try:
        result = subprocess.run(command, input=payload, text=True,
                                capture_output=True, timeout=15)
        accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
        record = {'exit_code': result.returncode, 'stdout': result.stdout,
                  'stderr_last_line': result.stderr.splitlines()[-1]
                  if result.stderr else ''}
    except subprocess.TimeoutExpired:
        accepted = False
        record = {'timeout': True}
    expected = case['expected'][profile]
    return {'profile': profile, 'case': case['name'], 'optimized': optimized,
            'expected': expected, 'accepted': accepted,
            'passed': accepted == expected, **record}


def verify(write=False):
    manifest = json.loads((ROOT / 'evidence/source_manifest.json').read_text())
    for relative, digest in manifest['sha256'].items():
        actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        if actual != digest:
            raise ValueError('Frozen source/fixture changed: ' + relative)
    metrics = [measure(ROOT / 'code' / (name + '.py')) for name in PROFILES]
    rows = []
    for filename in ('baseline_cases.json', 'new_cases.json', 'common_cases.json'):
        for case in json.loads((ROOT / 'tests' / filename).read_text()):
            for profile in case['expected']:
                for optimized in (False, True):
                    rows.append(run_case(profile, case, optimized))
    runtime = {'python': sys.version, 'python_implementation': platform.python_implementation(),
               'zlib_build': zlib.ZLIB_VERSION,
               'zlib_runtime': zlib.ZLIB_RUNTIME_VERSION}
    failures = [row for row in rows if not row['passed']]
    summary = {'runtime': runtime, 'process_runs': len(rows),
               'accepts': sum(row['accepted'] for row in rows),
               'rejects': sum(not row['accepted'] for row in rows),
               'failures': len(failures), 'metrics': metrics}
    if write:
        (ROOT / 'evidence/validation.json').write_text(
            json.dumps({'summary': summary, 'runs': rows}, indent=2) + '\n')
        (ROOT / 'evidence/metrics.json').write_text(
            json.dumps({'runtime': runtime, 'measurements': metrics}, indent=2) + '\n')
    print(json.dumps(summary, indent=2))
    if failures:
        print(json.dumps(failures, indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true',
                        help='Regenerate the runtime and validation receipts.')
    verify(parser.parse_args().write)
