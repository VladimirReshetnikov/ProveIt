"""Verify delivered hashes and replay the self-contained checker comparison."""
from pathlib import Path
import argparse
import hashlib
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdf', action='store_true')
    parser.add_argument('--skip-manifest', action='store_true',
                        help='For deliberate local edits after the initial verification.')
    args = parser.parse_args()
    manifest = ROOT / 'MANIFEST.sha256'
    if not args.skip_manifest:
        if not manifest.exists():
            raise SystemExit('MANIFEST.sha256 is missing')
        entries = 0
        for line in manifest.read_text().splitlines():
            expected, name = line.split('  ', 1)
            actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            if actual != expected:
                raise SystemExit('Hash mismatch: ' + name)
            entries += 1
        print(f'Verified {entries} delivered files.', flush=True)
    subprocess.run([sys.executable, str(ROOT / 'checker/verify.py')],
                   cwd=ROOT, check=True)
    if args.pdf:
        subprocess.run([sys.executable, str(ROOT / 'assemble.py')],
                       cwd=ROOT, check=True)
        subprocess.run([sys.executable, str(ROOT / 'build_pdf.py')],
                       cwd=ROOT, check=True)


if __name__ == '__main__':
    main()
