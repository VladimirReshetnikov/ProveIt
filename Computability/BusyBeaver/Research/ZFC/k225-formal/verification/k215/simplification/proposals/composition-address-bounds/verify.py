#!/usr/bin/env python3
"""Release identities and lightweight checks; no proof compilation or state solver."""
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def check_manifest():
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    for item in manifest['files']:
        p = ROOT / item['path']
        if (not p.is_file() or p.stat().st_size != item['bytes'] or
                hashlib.sha256(p.read_bytes()).hexdigest() != item['sha256']):
            raise SystemExit('Identity mismatch: ' + item['path'])
    print('PASS_RELEASE_IDENTITIES', len(manifest['files']), flush=True)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--hashes-only', action='store_true')
    ap.add_argument('--work-dir', type=Path, help='existing parent for temporary replay directory')
    args = ap.parse_args()
    if sys.flags.optimize:
        raise SystemExit('Run without -O: component replays use Python assertions.')
    check_manifest()
    if not args.hashes_only:
        # Some component scripts write evidence. Replay in a temporary copy,
        # so the release and its recorded evidence remain byte-for-byte intact.
        with tempfile.TemporaryDirectory(prefix='k215-replay-', dir=args.work_dir) as tmp:
            work = Path(tmp)
            for folder in ('normalized_balanced', 'address_runs'):
                shutil.copytree(ROOT / folder, work / folder)
            for folder, script in [
                ('normalized_balanced', 'lookup_metrics.py'),
                ('address_runs', 'verify.py'),
                ('address_runs', 'check_capacity.py'),
            ]:
                print('RUN', folder, script, flush=True)
                subprocess.run([sys.executable, '-B', script],
                               cwd=work / folder, check=True)
    print('PASS_PACKET_CHECKS', flush=True)

if __name__ == '__main__':
    main()
