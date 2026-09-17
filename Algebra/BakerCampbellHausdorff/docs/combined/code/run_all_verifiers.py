#!/usr/bin/env python3
"""Run the three exact verifiers that accompany the source papers.

Usage:
    python code/run_all_verifiers.py [--degree N] [--keep DIR]

Each verifier is executed unchanged from its own directory
(../paper-1/code, ../paper-2/code, ../paper-3/code) with its output redirected
to a scratch directory, so the papers' committed data files are not touched.
The printed reports are collected into data/verification_summary.json.

Python 3.10+, standard library only.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
COMBINED = HERE.parent
DOCS = COMBINED.parent

VERIFIERS = [
    # (label, paper dir, argument builder)
    ('paper-1', DOCS / 'paper-1', lambda d, out: ['--degree', str(d), '--output', str(out)]),
    ('paper-2', DOCS / 'paper-2', lambda d, out: ['--degree', str(max(d, 12)), '--check-degree', str(d), '--out', str(out)]),
    ('paper-3', DOCS / 'paper-3', lambda d, out: ['--degree', str(d), '--out', str(out)]),
]

PASS_RE = re.compile(r'^\s*(PASS|FAIL)\b', re.IGNORECASE)


def run_one(label: str, paper: Path, args: list[str], out: Path) -> dict:
    script = paper / 'code' / 'verify_bch.py'
    out.mkdir(parents=True, exist_ok=True)
    cmd = [sys.executable, str(script), *args]
    print(f'+ ({label}) ' + ' '.join(cmd), flush=True)
    t0 = time.time()
    proc = subprocess.run(cmd, cwd=paper, capture_output=True, text=True)
    elapsed = time.time() - t0
    lines = proc.stdout.splitlines()
    passes = [ln.strip() for ln in lines if PASS_RE.match(ln) and ln.strip().upper().startswith('PASS')]
    fails = [ln.strip() for ln in lines if PASS_RE.match(ln) and ln.strip().upper().startswith('FAIL')]
    if not passes and not fails:
        # paper-2 prints its JSON report; count the per-test status fields.
        try:
            report = json.loads(proc.stdout[proc.stdout.index('{'):])
            for t in report.get('tests', []):
                line = f"{t.get('status', '?')}: {t.get('test', '?')} (through degree {t.get('through_degree', '?')})"
                (passes if str(t.get('status', '')).upper() == 'PASS' else fails).append(line)
        except (ValueError, KeyError):
            pass
    print(proc.stdout)
    if proc.returncode != 0:
        print(proc.stderr, file=sys.stderr)
    return {
        'label': label,
        'command': cmd,
        'returncode': proc.returncode,
        'elapsed_seconds': round(elapsed, 3),
        'passed_checks': len(passes),
        'failed_checks': len(fails),
        'pass_lines': passes,
        'fail_lines': fails,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--degree', type=int, default=10, help='cross-check degree (default 10)')
    parser.add_argument('--keep', type=Path, default=None,
                        help='directory in which to keep the verifiers\' output (default: temporary)')
    a = parser.parse_args()
    base = a.keep if a.keep is not None else Path(tempfile.mkdtemp(prefix='bch_verify_'))
    results = []
    for label, paper, build in VERIFIERS:
        results.append(run_one(label, paper, build(a.degree, base / label), base / label))
    summary = {
        'cross_check_degree': a.degree,
        'output_directory': str(base),
        'results': results,
        'all_passed': all(r['returncode'] == 0 and r['failed_checks'] == 0 for r in results),
        'total_passed_checks': sum(r['passed_checks'] for r in results),
    }
    target = COMBINED / 'data' / 'verification_summary.json'
    target.write_text(json.dumps(summary, indent=2), encoding='utf-8')
    print(f"Summary written to {target}: {summary['total_passed_checks']} passed checks, "
          f"all_passed={summary['all_passed']}")
    return 0 if summary['all_passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
