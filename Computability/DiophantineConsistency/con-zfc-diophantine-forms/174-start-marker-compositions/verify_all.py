#!/usr/bin/env python3
"""Verify the sealed release, all new finite data, and its printed appendices.

Python 3.10+, standard library only, no network or root search.  These checks
are not a formal proof of the inherited unbounded arithmetic calibrations.
--optimized runs each component with Python -O as an additional option.
--manifest-only checks the complete delivered file inventory and every hash.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
IGNORED_SUFFIXES = {'.aux', '.log', '.out', '.toc', '.pyc', '.synctex'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def artifact_files():
    return sorted(p for p in ROOT.rglob('*')
                  if p.is_file() and '__pycache__' not in p.parts
                  and not any(part.startswith('.') for part in p.relative_to(ROOT).parts)
                  and p.suffix not in IGNORED_SUFFIXES
                  and p != ROOT / 'MANIFEST_SHA256.json')


def manifest_check():
    manifest = json.loads((ROOT / 'MANIFEST_SHA256.json').read_text())
    actual = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in artifact_files()}
    expected = manifest['files']
    require(set(actual) == set(expected),
            'Manifest inventory mismatch: missing=' + str(sorted(set(expected) - set(actual)))
            + '; extra=' + str(sorted(set(actual) - set(expected))))
    mismatches = [name for name in expected if actual[name] != expected[name]]
    require(not mismatches, 'Manifest digest mismatch: ' + str(mismatches))
    return {'status': 'PASS', 'files': len(actual), 'algorithm': 'SHA-256'}


def run_component(job, optimized):
    label, arguments = job
    command = [sys.executable, '-B'] + (['-O'] if optimized else []) + arguments
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(result.returncode == 0, label + ' failed:\n' + result.stdout + '\n' + result.stderr)
    try:
        report = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise ValueError(label + ' did not return a JSON receipt:\n' + result.stdout) from error
    require(report.get('status') == 'PASS', label + ' did not report PASS')
    return label, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--manifest-only', action='store_true')
    arguments = parser.parse_args()
    manifest = manifest_check()
    reports = {}
    if not arguments.manifest_only:
        jobs = [
            ('compact_4127_generator', ['compact66/preferred4127/start_only.py']),
            ('compact_4159_generator', ['compact66/intermediate4159/start_only.py']),
            ('compact_4127_independent', ['checks/review_compact.py', '4127']),
            ('compact_4159_independent', ['checks/review_compact.py', '4159']),
            ('positive_85_coefficients', ['positive85/build_coefficients.py']),
            ('positive_85_graph_and_map', ['positive85/verify.py']),
            ('direct_233_projections', ['direct233/verify.py']),
            ('printed_appendices', ['build_appendices.py', '--check']),
        ]
        with ThreadPoolExecutor(max_workers=4) as pool:
            futures = [pool.submit(run_component, job, arguments.optimized) for job in jobs]
            for future in futures:
                label, report = future.result()
                reports[label] = report
        # Every component is invoked read-only; validate that fact as well.
        require(manifest_check() == manifest, 'A verification step modified a sealed artifact')
    print(json.dumps({
        'status': 'PASS', 'python_optimized_components': arguments.optimized,
        'scope': 'Exact finite artifacts and their print bindings; ordinary and inherited mathematical proofs are separate.',
        'manifest': manifest, 'components': reports,
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
