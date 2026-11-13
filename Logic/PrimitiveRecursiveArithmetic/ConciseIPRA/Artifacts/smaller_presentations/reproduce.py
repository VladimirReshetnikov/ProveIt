"""Recompute complete-source metrics and replay the packaged certificates.

This is an untrusted reproduction harness. No checker imports this file.
The checker acceptance convention is status zero and exactly 'ACCEPT\n'.
"""
from pathlib import Path
import argparse
import ast
import concurrent.futures
import gzip
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize
import zlib

sys.dont_write_bytecode = True
from recode_certificate import convert

ROOT = Path(__file__).resolve().parent
IGNORED = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
    tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}


def measure(path):
    raw = path.read_bytes()
    normalized = ast.unparse(ast.parse(raw.decode('utf-8'))) + '\n'
    data = normalized.encode('utf-8')
    return {
        'file': str(path.relative_to(ROOT)),
        'tokens': sum(t.type not in IGNORED for t in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
        'normalized_bytes': len(data),
        'gzip9_normalized_bytes': len(gzip.compress(data, compresslevel=9, mtime=0)),
        'raw_bytes': len(raw),
        'gzip9_raw_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
        'sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(data).hexdigest(),
    }


def manifest_errors():
    manifest = ROOT / 'SHA256SUMS.txt'
    if not manifest.exists():
        return ['No manifest is present.']
    failures = []
    for line in manifest.read_text().splitlines():
        digest, name = line.split('  ', 1)
        p = ROOT / name
        if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest() != digest:
            failures.append(name)
    return failures


def execute(job):
    case, checker, optimized = job
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(ROOT / checker))
    try:
        run = subprocess.run(command, input=(ROOT / case['file']).read_bytes(),
                             capture_output=True, timeout=15)
        accepted = run.returncode == 0 and run.stdout == b'ACCEPT\n'
        error = None
    except subprocess.TimeoutExpired:
        accepted, error = False, 'timeout'
    expected = case.get('expected_by_checker', {}).get(checker, case['expected'])
    return {
        'fixture': case['file'], 'checker': checker, 'optimized': optimized,
        'accepted': accepted, 'expected': expected,
        'passed': accepted == expected, 'error': error,
    }


def check_recodings():
    transformations = json.loads((ROOT / 'fixtures/recodings.json').read_text())
    failures = []
    for item in transformations:
        original = json.loads((ROOT / item['source']).read_text())
        expected = json.loads((ROOT / item['target']).read_text())
        if convert(original) != expected:
            failures.append(item)
    return len(transformations), failures


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        help='Write a JSON receipt to this path; otherwise print it.')
    parser.add_argument('--metrics-only', action='store_true')
    parser.add_argument('--skip-manifest', action='store_true',
                        help='For working copies before their final manifest is built.')
    parser.add_argument('--pdf', action='store_true')
    args = parser.parse_args()
    paths = sorted((ROOT / 'code').glob('checker*.py'))
    paths += sorted((ROOT / 'controls').glob('*.py'))
    measurements = [measure(p) for p in paths]
    expected_file = ROOT / 'evidence/expected_metrics.json'
    expected = json.loads(expected_file.read_text()) if expected_file.exists() else {}
    metric_failures = []
    if platform.python_version() == '3.12.14':
        for row in measurements:
            for key, value in expected.get(row['file'], {}).items():
                if row[key] != value:
                    metric_failures.append([row['file'], key, value, row[key]])
    cases = json.loads((ROOT / 'fixtures/cases.json').read_text())
    jobs = [(case, checker, optimized) for case in cases
            for checker in case['checkers'] for optimized in (False, True)]
    results = []
    if not args.metrics_only:
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
            results = list(pool.map(execute, jobs))
    recoding_count, recoding_failures = check_recodings()
    integrity_failures = [] if args.skip_manifest else manifest_errors()
    if args.pdf:
        for _ in range(2):
            subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                            'report.tex'], cwd=ROOT, check=True, capture_output=True)
    failures = [r for r in results if not r['passed']]
    report = {
        'python': platform.python_version(), 'zlib': zlib.ZLIB_RUNTIME_VERSION,
        'normalization': 'Whole module ast.unparse plus LF; no docstring removal',
        'measurements': measurements, 'metric_failures': metric_failures,
        'fixture_count': len({case['file'] for case in cases}),
        'case_entries': len(cases), 'executions': len(results),
        'recoding_count': recoding_count, 'recoding_failures': recoding_failures,
        'test_failures': failures, 'manifest_failures': integrity_failures,
        'results': results,
        'passed': not (failures or metric_failures or integrity_failures
                       or recoding_failures),
    }
    text = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
        print(json.dumps({k: report[k] for k in
                          ['python', 'fixture_count', 'executions', 'passed']}))
    else:
        print(text, end='')
    if not report['passed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
