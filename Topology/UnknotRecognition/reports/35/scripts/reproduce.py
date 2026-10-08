#!/usr/bin/env python3
"""Verify the distribution, run its maintained suite, or rerun optional benchmarks."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
FAST = ROOT / 'source/Topology/UnknotRecognition/fast'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify():
    manifest = ROOT / 'SHA256SUMS'
    if not manifest.exists():
        raise SystemExit('SHA256SUMS is absent; this is not a finalized distribution.')
    count = 0
    for line in manifest.read_text().splitlines():
        expected, rel = line.split('  ', 1)
        path = ROOT / rel
        if not path.is_file() or digest(path) != expected:
            raise SystemExit(f'Hash mismatch: {rel}')
        count += 1
    provenance = json.loads((ROOT / 'SOURCE_MANIFEST.json').read_text())
    for key, folder in [('source_sha256', 'source'), ('baseline_sha256', 'baseline')]:
        for rel, expected in provenance[key].items():
            if digest(ROOT / folder / rel) != expected:
                raise SystemExit(f'Source provenance mismatch: {folder}/{rel}')
    evidence = json.loads((ROOT / 'evidence/surface_gluing_20261008.json').read_text())
    for rel, expected in evidence['metadata']['source_sha256'].items():
        if digest(ROOT / 'evidence/measured_sources' / rel) != expected:
            raise SystemExit(f'Measured source mismatch: {rel}')
    with tempfile.TemporaryDirectory(prefix='unknot_patch_check_') as temp:
        target = Path(temp)
        shutil.copytree(ROOT / 'baseline', target, dirs_exist_ok=True)
        patch = ROOT / 'integration/changes.patch'
        subprocess.run(['git', 'apply', '--check', str(patch)], cwd=target, check=True)
        subprocess.run(['git', 'apply', str(patch)], cwd=target, check=True)
        actual = {p.relative_to(target).as_posix(): digest(p)
                  for p in target.rglob('*') if p.is_file()}
        if actual != provenance['source_sha256']:
            missing = sorted(set(provenance['source_sha256']) - set(actual))
            extra = sorted(set(actual) - set(provenance['source_sha256']))
            different = sorted(p for p in set(actual) & set(provenance['source_sha256'])
                               if actual[p] != provenance['source_sha256'][p])
            raise SystemExit(f'Patch reproduction mismatch: missing={missing}, extra={extra}, changed={different}')
    print(f'Verified {count} file hashes, measured sources, and byte-identical patch reproduction.')
    print('Baseline:', provenance['baseline_commit'])


def tests():
    subprocess.run([sys.executable, '-B', '-m', 'unittest', 'discover', '-s', 'tests', '-v'],
                   cwd=FAST, check=True)


def benchmarks():
    output = ROOT / 'rerun_results'
    output.mkdir(exist_ok=True)
    subprocess.run([sys.executable, '-B', 'benchmark_primary_split.py', '--output',
                    str(output / 'primary_split.json'), '--rounds', '7', '--batches', '10'],
                   cwd=FAST, check=True)
    subprocess.run([sys.executable, '-B', '-m', 'gluing_research.benchmark', '--output',
                    str(output / 'surface_gluing.json'), '--rounds', '5'], cwd=FAST, check=True)
    print('Fresh benchmarks are in', output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true', help='Check hashes and replay the integration patch; requires git.')
    parser.add_argument('--tests', action='store_true', help='Run the complete maintained unittest suite.')
    parser.add_argument('--benchmarks', action='store_true', help='Rerun both longer benchmark drivers.')
    args = parser.parse_args()
    if not any(vars(args).values()):
        parser.print_help()
        return
    if args.verify:
        verify()
    if args.tests:
        tests()
    if args.benchmarks:
        benchmarks()


if __name__ == '__main__':
    main()
