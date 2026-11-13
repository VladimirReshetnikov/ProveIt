"""Reproduce the 581-byte checker's comparison with its pinned 584-byte control.

Requires only Python's standard library. By default, checker581.py,
control584.py, and floor_cases.json are siblings of this script. Paths can
also be supplied explicitly. Run with CPython 3.12.14 to reproduce the
recorded normalized-source measurements exactly.

Example:
    python3 verify_floor.py --receipt floor_validation.json

This verifier and its fixtures are untrusted test artifacts and are not
part of either proof-checker's trusted implementation.
"""

import argparse
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
import zlib


HERE = Path(__file__).resolve().parent
IGNORED = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT, tokenize.DEDENT,
    tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT,
}


def measure(path):
    raw = path.read_bytes()
    normalized = (ast.unparse(ast.parse(raw.decode('utf-8'))) + '\n').encode('utf-8')
    return {
        'file': path.name,
        'sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized).hexdigest(),
        'significant_tokens': sum(
            t.type not in IGNORED
            for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
        ),
        'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
        'normalized_bytes': len(normalized),
        'gzip9_normalized_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
    }


def run(job):
    path, case, optimized, timeout = job
    result = {
        'program': path.name,
        'case': case['name'],
        'optimized': optimized,
        'expected': case['expected'],
    }
    try:
        process = subprocess.run(
            [sys.executable, *(['-O'] if optimized else []), str(path)],
            input=json.dumps(case['certificate']), text=True,
            capture_output=True, timeout=timeout,
        )
        result['exit_code'] = process.returncode
        result['accepted'] = process.returncode == 0 and process.stdout == 'ACCEPT\n'
        result['passed'] = result['accepted'] == case['expected']
        if not result['passed']:
            result['stdout'] = process.stdout
            result['stderr'] = process.stderr[-2000:]
    except (OSError, subprocess.TimeoutExpired) as error:
        result.update(passed=False, error=type(error).__name__, detail=str(error))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', type=Path, default=HERE / 'checker581.py')
    parser.add_argument('--control', type=Path, default=HERE / 'control584.py')
    parser.add_argument('--fixtures', type=Path, default=HERE / 'floor_cases.json')
    parser.add_argument('--receipt', type=Path)
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--timeout', type=float, default=20)
    args = parser.parse_args()
    if args.workers < 1 or args.timeout <= 0:
        parser.error('--workers and --timeout must be positive')
    paths = [args.control.resolve(), args.checker.resolve()]
    cases = json.loads(args.fixtures.read_text())['cases']
    if not cases or any(type(c.get('expected')) is not bool for c in cases):
        parser.error('fixtures must contain nonempty cases with Boolean expectations')
    jobs = [
        (path, case, optimized, args.timeout)
        for path in paths for case in cases for optimized in (False, True)
    ]
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as executor:
        results = list(executor.map(run, jobs))
    failures = [result for result in results if not result['passed']]
    receipt = {
        'python': sys.version,
        'zlib_version': zlib.ZLIB_VERSION,
        'normalization': 'ast.unparse plus one LF',
        'measurements': [measure(path) for path in paths],
        'fixture_sha256': hashlib.sha256(args.fixtures.read_bytes()).hexdigest(),
        'cases': len(cases),
        'runs': len(results),
        'failures': failures,
        'results': results,
    }
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'results'}, indent=2))
    return 1 if failures else 0


if __name__ == '__main__':
    raise SystemExit(main())
