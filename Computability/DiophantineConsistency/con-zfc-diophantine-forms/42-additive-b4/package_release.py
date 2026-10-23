#!/usr/bin/env python3
"""Create or check the repository-ready artifact manifest and ZIP."""
from pathlib import Path
from hashlib import sha256
from zipfile import ZipFile, ZipInfo, ZIP_DEFLATED
import argparse
import json

ROOT = Path(__file__).resolve().parent
IGNORED_SUFFIXES = {".aux", ".fdb_latexmk", ".fls", ".log", ".out", ".toc", ".pyc", ".zip"}


def included(path):
    return (path.is_file() and "__pycache__" not in path.parts
            and path.suffix not in IGNORED_SUFFIXES
            and not any(part.startswith(".") for part in path.relative_to(ROOT).parts))


def entries():
    return {
        p.relative_to(ROOT).as_posix(): {
            "sha256": sha256(p.read_bytes()).hexdigest(),
            "bytes": p.stat().st_size,
        }
        for p in sorted(ROOT.rglob("*"))
        if included(p) and p.name != "MANIFEST.json"
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Verify existing manifest without writing.")
    parser.add_argument("--archive", type=Path, default=ROOT.parent / "ConZFC_Additive_Coding_2026-10-23.zip")
    args = parser.parse_args()
    manifest_path = ROOT / "MANIFEST.json"
    current = entries()
    if args.check:
        stored = json.loads(manifest_path.read_text())["files"]
        if current != stored:
            different = sorted(k for k in set(current) | set(stored) if current.get(k) != stored.get(k))
            raise SystemExit("Manifest differs: " + ", ".join(different))
        print(f"PASS: {len(current)} files match MANIFEST.json.")
        return
    if not (ROOT / "report.pdf").is_file():
        raise SystemExit("Build report.pdf first.")
    if json.loads((ROOT / "REPRODUCTION.json").read_text())["status"] != "PASS":
        raise SystemExit("Run reproduce.py successfully before packaging.")
    manifest_path.write_text(json.dumps({
        "algorithm": "SHA-256",
        "scope": "Delivered files, excluding this manifest and rebuild intermediates.",
        "files": current,
    }, indent=2) + "\n")
    with ZipFile(args.archive, "w", compression=ZIP_DEFLATED, compresslevel=9) as archive:
        for relative in sorted([*current, "MANIFEST.json"]):
            info = ZipInfo("con-zfc-additive-coding/" + relative, date_time=(2026, 10, 23, 0, 0, 0))
            info.compress_type = ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, (ROOT / relative).read_bytes(), compresslevel=9)
    with ZipFile(args.archive) as archive:
        if archive.testzip() is not None:
            raise SystemExit("ZIP integrity check failed.")
    print(f"Created {args.archive}: {len(current)+1} files, {args.archive.stat().st_size} bytes.")


if __name__ == "__main__":
    main()
