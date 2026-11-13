"""Verify the distribution and rerun its checks in a private temporary copy."""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, sys, tempfile

ROOT = Path(__file__).resolve().parent

def check_manifest():
    manifest = ROOT / 'MANIFEST.sha256'
    if not manifest.exists():
        raise RuntimeError('The distribution manifest is missing')
    count = 0
    for line in manifest.read_text().splitlines():
        expected, relative = line.split('  ', 1)
        actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError('Checksum mismatch: ' + relative)
        count += 1
    print('Manifest:', count, 'files verified', flush=True)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pdf', action='store_true')
    parser.add_argument('--manifest-only', action='store_true')
    args = parser.parse_args()
    check_manifest()
    if args.manifest_only:
        return
    with tempfile.TemporaryDirectory(prefix='ipra-reproduce-') as temporary:
        work = Path(temporary) / 'package'
        shutil.copytree(ROOT, work, ignore=shutil.ignore_patterns('__pycache__', 'build'))
        tasks = [
            ('complete checker regressions', ['code/checkers/verify.py']),
            ('AQE symbolic and CLI checks', ['code/abstraction/verify.py']),
            ('independent AQE checks', ['code/abstraction/independent_checks.py']),
            ('independent AQE checks under -O', ['-O', 'code/abstraction/independent_checks.py']),
            ('predecessor syntax and values', ['mathematics/predecessor45.py']),
            ('pinned source census', ['code/census.py']),
        ]
        for title, command in tasks:
            result = subprocess.run([sys.executable, *command], cwd=work,
                                    capture_output=True, text=True, timeout=900)
            if result.returncode:
                print(result.stdout)
                print(result.stderr, file=sys.stderr)
                raise SystemExit(result.returncode)
            print(title + ': PASS', flush=True)
        if args.pdf:
            subprocess.run([sys.executable, 'build_report.py', '--pdf'], cwd=work, check=True)
            print('PDF build: PASS', flush=True)
    print('All requested reproduction checks passed. Original files are unchanged.')

if __name__ == '__main__':
    main()
