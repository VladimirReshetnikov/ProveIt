"""Reproduce the supplied metrics, certificate checks, and optional PDF."""
import argparse
import hashlib
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def manifest():
    count = 0
    for line in (ROOT / 'MANIFEST.sha256').read_text().splitlines():
        expected, name = line.split('  ', 1)
        actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        if expected != actual:
            raise ValueError('Manifest mismatch: ' + name)
        count += 1
    print('Manifest verified:', count, 'files')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-only', action='store_true')
    parser.add_argument('--pdf', action='store_true')
    args = parser.parse_args()
    if (ROOT / 'MANIFEST.sha256').exists():
        manifest()
    if args.manifest_only:
        return
    for script in ('measure.py', 'verify.py'):
        subprocess.run([sys.executable, '-B', str(ROOT / script)], check=True, cwd=ROOT)
    if args.pdf:
        from pdf_build_support import build
        build(ROOT / 'report.tex', ROOT / 'ipra_shared_leaf.pdf',
              ROOT / 'evidence/pdf_build.log')


if __name__ == '__main__':
    main()
