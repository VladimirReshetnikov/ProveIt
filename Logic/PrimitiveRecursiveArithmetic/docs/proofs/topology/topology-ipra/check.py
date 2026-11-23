"""Replay the finite examples and verify each copied upstream file, offline."""
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
COMPANIONS = ROOT / 'companions'


def verify_upstream():
    records = json.loads((ROOT / 'upstream.json').read_text())['files']
    for record in records:
        data = (ROOT / record['path']).read_bytes()
        header = f'blob {len(data)}\0'.encode()
        if hashlib.sha1(header + data).hexdigest() != record['git_blob']:
            raise ValueError(f"Git blob mismatch for {record['path']}")
    print(f"Verified {len(records)} pinned Git blobs.", flush=True)


def run(script, *args):
    cmd = [sys.executable, '-B', str(script), *map(str, args)]
    print(f"\nRunning {script.relative_to(ROOT)}", flush=True)
    subprocess.run(cmd, check=True, cwd=ROOT)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--main-only', action='store_true',
                        help='skip the three companion test suites')
    args = parser.parse_args()
    if not __debug__:
        parser.error('The checks require ordinary Python without -O.')
    verify_upstream()
    for script in sorted((ROOT / 'code').glob('*_checks.py')):
        run(script)
    if args.main_only:
        return
    run(COMPANIONS / 'approximate_brouwer_ipra/code/test_brouwer.py')
    run(COMPANIONS / 'hairy_ball_ipra/code/hairy_ball.py', '--self-test')
    run(COMPANIONS / 'hairy_ball_ipra/code/round_witness.py', '--test')
    with tempfile.TemporaryDirectory() as tmp:
        run(COMPANIONS / 'dimension_invariance_ipra/code/validate.py',
            '--output', Path(tmp) / 'dimension.json')
    print('\nAll checks passed.', flush=True)


if __name__ == '__main__':
    main()
