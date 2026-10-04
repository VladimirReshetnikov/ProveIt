#!/usr/bin/env python3
"""Create a deterministic ZIP of this already sealed release."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import zipfile
ROOT = Path(__file__).resolve().parent
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists():
        raise RuntimeError('Choose a new output path; existing artifacts are preserved.')
    if output == ROOT or ROOT in output.parents:
        raise RuntimeError('Archive must be outside the release directory.')
    subprocess.run([sys.executable, str(ROOT / 'verify_release.py')], check=True)
    output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for p in sorted(ROOT.rglob('*')):
            if not p.is_file():
                continue
            info = zipfile.ZipInfo('square-product82-report45/' + str(p.relative_to(ROOT)),
                                   date_time=(2026,10,4,0,0,0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(info, p.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    print(json.dumps({'status': 'PASS', 'sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
                      'bytes': output.stat().st_size}, sort_keys=True))
if __name__ == '__main__':
    main()

