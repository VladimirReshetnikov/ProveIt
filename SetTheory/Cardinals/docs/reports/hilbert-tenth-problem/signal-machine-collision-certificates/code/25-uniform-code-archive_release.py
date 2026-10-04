#!/usr/bin/env python3
"""Create a deterministic ZIP of the sealed release at a new external path."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import zipfile
from verify_release import ROOT, inventory, verify
from replay import require


def archive(raw):
    verification = verify()
    absolute = Path(os.path.abspath(raw))
    require(all(not p.is_symlink() for p in (absolute, *absolute.parents)), 'Output symlink rejected')
    target = absolute.resolve()
    require(target != ROOT and ROOT not in target.parents, 'Archive must be external to release')
    require(not target.exists(), 'Archive output must not already exist')
    require(target.parent.is_dir(), 'Archive output parent must exist')
    with zipfile.ZipFile(target, 'x', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for rel in inventory():
            info = zipfile.ZipInfo('Research_Report51/' + rel, (2026, 10, 4, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.create_system = 3
            info.external_attr = (0o100444 << 16)
            z.writestr(info, (ROOT / rel).read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    with zipfile.ZipFile(target) as z:
        require(z.testzip() is None, 'ZIP CRC failure')
        require(len(z.infolist()) == len(inventory()), 'ZIP member count mismatch')
    return {'status': 'PASS', 'archive': str(target), 'bytes': target.stat().st_size,
            'sha256': hashlib.sha256(target.read_bytes()).hexdigest(), 'release': verification}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(archive(args.output), indent=2, sort_keys=True))
