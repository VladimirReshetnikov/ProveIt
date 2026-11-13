"""Reproduce the supplied research artifacts without network access."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def verify_manifest():
    file = ROOT / 'MANIFEST.sha256'
    if not file.is_file():
        raise RuntimeError('MANIFEST.sha256 is missing.')
    count = 0
    for line in file.read_text().splitlines():
        if not line.strip():
            continue
        expected, relative = line.split('  ', 1)
        path = ROOT / relative
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError('Manifest mismatch: ' + relative)
        count += 1
    return count


def run(relative):
    result = subprocess.run([sys.executable, '-B', str(ROOT / relative)],
                            cwd=ROOT, capture_output=True, text=True, timeout=180)
    if result.returncode:
        print(result.stdout)
        print(result.stderr, file=sys.stderr)
        raise RuntimeError('Reproduction failed: ' + relative)
    print(relative + ': passed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdf', action='store_true', help='Rebuild the PDF in three passes.')
    parser.add_argument('--verify-only', action='store_true', help='Check exact delivered file hashes only.')
    args = parser.parse_args()
    count = verify_manifest()
    print('Manifest: verified ' + str(count) + ' files')
    if args.verify_only:
        return
    for relative in ('measure.py', 'code/verify_census.py', 'code/verify_stream.py', 'code/verify_bytes.py',
                     'code/verify_validated.py', 'code/check_compute_leaf.py',
                     'code/predecessor45.py'):
        run(relative)
    if args.pdf:
        from pdf_build_support import build
        build(ROOT / 'report.tex', ROOT / 'ipra_computation_leaves.pdf',
              ROOT / 'evidence' / 'pdf_build.log')
    print('Reproduction completed. Regenerated receipts/PDF may differ in environment metadata.')


if __name__ == '__main__':
    main()
