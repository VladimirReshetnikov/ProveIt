#!/usr/bin/env python3
"""Build the complete deterministic release ZIP and content manifest."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent
EXCLUDED_SUFFIXES = {".aux", ".log", ".out", ".toc", ".pyc", ".fls", ".fdb_latexmk", ".synctex.gz"}


def include(p):
    rel = p.relative_to(ROOT)
    return (p.is_file() and "__pycache__" not in rel.parts
            and not any(part.startswith(".") for part in rel.parts)
            and p.suffix not in EXCLUDED_SUFFIXES
            and p.name not in {"MANIFEST.sha256"})


def main():
    if not (ROOT / "report.pdf").is_file():
        raise RuntimeError("Build report.pdf before making the release archive")
    receipt = ROOT / "verification/RELEASE_CHECKS.json"
    if not receipt.is_file() or json.loads(receipt.read_text())["status"] != "PASS":
        raise RuntimeError("Run verify.py successfully before making the release archive")
    files = sorted((p for p in ROOT.rglob("*") if include(p)), key=lambda p: str(p.relative_to(ROOT)))
    entries = [(p, hashlib.sha256(p.read_bytes()).hexdigest()) for p in files]
    manifest = ROOT / "MANIFEST.sha256"
    manifest.write_text("".join(f"{h}  {p.relative_to(ROOT).as_posix()}\n" for p, h in entries))
    target = ROOT.parent / (ROOT.name + ".zip")
    with zipfile.ZipFile(target, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for p in sorted(files + [manifest], key=lambda p: str(p.relative_to(ROOT))):
            name = ROOT.name + "/" + p.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 23, 12, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            z.writestr(info, p.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    with zipfile.ZipFile(target) as z:
        bad = z.testzip()
        if bad:
            raise RuntimeError("ZIP CRC failure: " + bad)
        for p, expected in entries:
            name = ROOT.name + "/" + p.relative_to(ROOT).as_posix()
            if hashlib.sha256(z.read(name)).hexdigest() != expected:
                raise RuntimeError("Archived byte mismatch: " + name)
    result = {"archive": target.name, "files": len(files) + 1, "bytes": target.stat().st_size,
              "sha256": hashlib.sha256(target.read_bytes()).hexdigest(), "crc_and_hashes": "PASS"}
    (ROOT.parent / (ROOT.name + ".release.json")).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
