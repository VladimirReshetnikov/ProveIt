"""Zip the tracked contents of this repository at maximum compression.

Includes every file tracked by git (so untracked files and .git are left out),
except this script. The archive is written to the repository root as
<root-directory-name>.zip and is itself ignored by git (*.zip).

Usage, from anywhere:  python make_archive.py
"""
from __future__ import annotations

import os
import subprocess
import sys
import zipfile

ROOT = os.path.dirname(os.path.abspath(__file__))
SELF = os.path.basename(__file__)


def tracked_files() -> list[str]:
    out = subprocess.run(["git", "ls-files", "-z"], cwd=ROOT, check=True,
                         capture_output=True).stdout
    return [p.decode("utf-8") for p in out.split(b"\0") if p]


def main() -> int:
    name = os.path.basename(ROOT) + ".zip"
    target = os.path.join(ROOT, name)
    files = [f for f in tracked_files() if f != SELF and os.path.isfile(os.path.join(ROOT, f))]
    with zipfile.ZipFile(target, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
        for f in sorted(files):
            zf.write(os.path.join(ROOT, f), arcname=f)
    size = os.path.getsize(target)
    print(f"{name}: {len(files)} files, {size:,} bytes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
