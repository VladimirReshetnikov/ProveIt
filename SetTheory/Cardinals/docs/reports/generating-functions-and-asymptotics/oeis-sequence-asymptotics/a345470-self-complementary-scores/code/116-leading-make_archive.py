#!/usr/bin/env python3
"""Reproduce the reader ZIP from its verified extracted contents."""
import argparse
from hashlib import sha256
from pathlib import Path
import sys
import zipfile
sys.dont_write_bytecode = True
from integrity import validate

ROOT = Path(__file__).resolve().parent

def archive(destination):
    validate(ROOT)
    destination = Path(destination).resolve()
    if destination.is_relative_to(ROOT):
        raise RuntimeError("Choose an output location outside the sealed package")
    files = sorted(path for path in ROOT.rglob("*") if path.is_file())
    with zipfile.ZipFile(destination, "w", compression=zipfile.ZIP_STORED) as zipped:
        for path in files:
            info = zipfile.ZipInfo("report116/" + path.relative_to(ROOT).as_posix(),
                                   date_time=(1980, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_STORED
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.flag_bits = 0
            zipped.writestr(info, path.read_bytes())
    return sha256(destination.read_bytes()).hexdigest()

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(archive(args.output))
