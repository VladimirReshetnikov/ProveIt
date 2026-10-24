#!/usr/bin/env python3
"""Create a reproducible source/PDF ZIP with a complete integrity manifest."""
from pathlib import Path
import hashlib
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
SKIP_SUFFIXES = {".aux", ".log", ".toc", ".out", ".pyc", ".synctex", ".fls", ".fdb_latexmk"}


def included(path):
    return (path.is_file() and "__pycache__" not in path.parts
            and path.suffix not in SKIP_SUFFIXES
            and not path.name.endswith(".synctex.gz")
            and path.name != "MANIFEST.sha256")


def main():
    target = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else ROOT.with_suffix(".zip")
    paths = sorted(path for path in ROOT.rglob("*") if included(path) and path != target)
    manifest = ROOT / "MANIFEST.sha256"
    manifest.write_text("".join(hashlib.sha256(path.read_bytes()).hexdigest() + "  "
                                + path.relative_to(ROOT).as_posix() + "\n"
                                for path in paths))
    paths = sorted(paths + [manifest])
    with zipfile.ZipFile(target, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in paths:
            info = zipfile.ZipInfo(ROOT.name + "/" + path.relative_to(ROOT).as_posix(),
                                   date_time=(2026, 10, 23, 0, 0, 0))
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(target) as archive:
        bad = archive.testzip()
        if bad:
            raise RuntimeError("Corrupt ZIP member: " + bad)
    print(str(target))
    print("files=" + str(len(paths)) + " bytes=" + str(target.stat().st_size)
          + " sha256=" + hashlib.sha256(target.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
