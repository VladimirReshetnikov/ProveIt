"""Verify this archive in a temporary copy; optionally rebuild its PDF."""
import argparse
import hashlib
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def manifest():
    ledger = ROOT / 'MANIFEST.sha256'
    if not ledger.exists():
        raise SystemExit('Missing MANIFEST.sha256')
    count = 0
    for line in ledger.read_text().splitlines():
        expected, relative = line.split('  ', 1)
        path = ROOT / relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise SystemExit('Manifest mismatch: ' + relative)
        count += 1
    print('Manifest verified:', count, 'files', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-only', action='store_true')
    parser.add_argument('--pdf', action='store_true')
    args = parser.parse_args()
    manifest()
    if args.manifest_only:
        return
    with tempfile.TemporaryDirectory(prefix='ipra_uniform_terminals_') as temp:
        work = Path(temp) / 'package'
        shutil.copytree(ROOT, work, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
        subprocess.run([sys.executable, 'tests/verify.py'], cwd=work, check=True)
        subprocess.run([sys.executable, 'mathematics/obstruction_diagnostic.py'], cwd=work, check=True)
        if args.pdf:
            for _ in range(2):
                result = subprocess.run(['pdflatex', '-interaction=nonstopmode',
                                         '-halt-on-error', 'report.tex'], cwd=work,
                                        text=True, stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT)
                if result.returncode:
                    print(result.stdout)
                    raise SystemExit(result.returncode)
            print('PDF rebuilt successfully in temporary copy.')
    print('All requested checks passed.')


if __name__ == '__main__':
    main()
