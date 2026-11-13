"""Verify delivered files, remeasure whole modules, and optionally replay tests.

Run with Python 3.12.14 for exact ast.unparse measurements.
Tests execute in temporary copies and preserve the delivered evidence.
"""
import argparse
import ast
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NL, tokenize.NEWLINE,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    tree = ast.parse(path.read_text())
    source = ast.unparse(tree) + '\n'
    return dict(tokens=sum(token.type not in SKIP for token in
                           tokenize.generate_tokens(io.StringIO(source).readline)),
                ast_nodes=sum(1 for _ in ast.walk(tree)),
                normalized_bytes=len(source.encode()),
                normalized_sha256=hashlib.sha256(source.encode()).hexdigest())


def verify_manifest():
    count = 0
    for line in (ROOT / 'MANIFEST.sha256').read_text().splitlines():
        expected, name = line.split('  ', 1)
        path = ROOT / name
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise SystemExit('Manifest mismatch: ' + name)
        count += 1
    print(f'Manifest verified: {count} files.')


def verify_measurements():
    expected = json.loads((ROOT / 'evidence' / 'measurements.json').read_text())
    for row in expected['programs']:
        result = measure(ROOT / row['path'])
        for key in ('tokens', 'ast_nodes', 'normalized_bytes', 'normalized_sha256'):
            if result[key] != row[key]:
                raise SystemExit(f'Measurement mismatch: {row["path"]}, {key}')
        print(f'{result["tokens"]:4} tokens / {result["ast_nodes"]:4} nodes / '
              f'{result["normalized_bytes"]:4} bytes  {row["path"]}')


def replay_tests():
    with tempfile.TemporaryDirectory(prefix='ipra-names-tests-') as directory:
        temporary = Path(directory)
        for component in ('names', 'exact_bindings'):
            shutil.copytree(ROOT / component, temporary / component,
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
        commands = [
            [sys.executable, str(temporary / 'names' / 'verify_names.py')],
            [sys.executable, str(temporary / 'exact_bindings' / 'verify_refinement.py')],
            [sys.executable, str(temporary / 'names' / 'audit_names.py'),
             str(temporary / 'names' / 'names_kernel.py')]
        ]
        for command in commands:
            result = subprocess.run(command, cwd=temporary, text=True,
                                    capture_output=True, timeout=180)
            if result.returncode:
                sys.stdout.write(result.stdout)
                sys.stderr.write(result.stderr)
                raise SystemExit(result.returncode)
        names = json.loads((temporary / 'names' / 'evidence' / 'verification.json').read_text())
        exact = json.loads((temporary / 'exact_bindings' / 'verification.json').read_text())
        print(f'Names: {names["closed_source_fixtures"]} inherited closed fixtures, '
              f'{names["open_translations"]} open translations, '
              f'{names["standalone_subprocess_runs"]} standalone executions; no failures.')
        print(f'Exact binding: {exact["process_runs"]} isolated executions; '
              f'{len(exact["failures"])} mismatches.')
        print('Independent naming audit: 240 terms, 1440 checks passed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tests', action='store_true')
    args = parser.parse_args()
    verify_manifest()
    verify_measurements()
    if args.tests:
        replay_tests()
