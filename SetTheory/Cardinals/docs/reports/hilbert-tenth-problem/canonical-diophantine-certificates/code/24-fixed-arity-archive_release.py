#!/usr/bin/env python3
"""Create one authenticated deterministic Report50 ZIP at a fresh external path."""
import argparse
import hashlib
from pathlib import Path
import sys
import zipfile
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_release import ROOT, authenticate, external_new, snapshot, need


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    authenticate(args.manifest_sha256)
    before = snapshot(ROOT)
    output = external_new(args.output)
    with output.open('xb') as stream:
        with zipfile.ZipFile(stream, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
            for path in sorted(ROOT.rglob('*')):
                if not path.is_file():
                    continue
                info = zipfile.ZipInfo('Research_Report50/'+path.relative_to(ROOT).as_posix(),
                    (2026, 10, 4, 0, 0, 0))
                info.create_system = 3
                info.external_attr = (0o100000 | (path.stat().st_mode & 0o777)) << 16
                info.compress_type = zipfile.ZIP_DEFLATED
                archive.writestr(info, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED,
                    compresslevel=9)
    need(snapshot(ROOT) == before, 'Release changed during archive creation')
    print('SHA256 '+hashlib.sha256(output.read_bytes()).hexdigest()+'  '+output.name)


if __name__ == '__main__':
    main()
