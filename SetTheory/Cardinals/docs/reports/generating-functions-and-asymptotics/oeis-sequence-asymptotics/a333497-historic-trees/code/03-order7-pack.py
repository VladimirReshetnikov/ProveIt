#!/usr/bin/env python3
"""Create a deterministic ZIP of the verified package, with fixed metadata."""
from pathlib import Path
import argparse
import hashlib
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parent

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('output', type=Path, help='ZIP path outside the package directory')
    args = ap.parse_args()
    destination = args.output.resolve()
    if destination == ROOT or ROOT in destination.parents:
        raise ValueError('ZIP output must be outside the package directory')
    subprocess.run([sys.executable, '-B', str(ROOT/'checks/check_manifest.py'), str(ROOT)], check=True)
    with zipfile.ZipFile(destination, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for source in sorted(ROOT.rglob('*')):
            if source.is_dir():
                continue
            name = 'report115/' + source.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 2, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, source.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    print('ZIP_PASS SHA256 ' + hashlib.sha256(destination.read_bytes()).hexdigest())

if __name__ == '__main__':
    main()
