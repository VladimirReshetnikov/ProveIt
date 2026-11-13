"""Create and verify a ZIP containing the complete research package."""
from pathlib import Path
import hashlib
import json
import sys
import zipfile


ROOT = Path(__file__).resolve().parent
EXCLUDED_DIRS = {"build", "__pycache__", ".git"}
EXCLUDED_SUFFIXES = {".aux", ".log", ".out", ".fmt", ".pyc", ".zip"}


def members():
    return sorted(
        p for p in ROOT.rglob("*")
        if p.is_file()
        and not (set(p.relative_to(ROOT).parts) & EXCLUDED_DIRS)
        and p.suffix not in EXCLUDED_SUFFIXES
        and p.name != "MANIFEST.sha256"
    )


def main():
    destination = (
        Path(sys.argv[1]).resolve() if len(sys.argv) > 1
        else ROOT.parent / "output" / (ROOT.name + ".zip")
    )
    if destination.is_relative_to(ROOT):
        raise SystemExit("Write the ZIP outside the package directory.")
    destination.parent.mkdir(parents=True, exist_ok=True)
    files = members()
    ledger = "".join(
        hashlib.sha256(p.read_bytes()).hexdigest()
        + "  " + p.relative_to(ROOT).as_posix() + "\n"
        for p in files
    )
    manifest = ROOT / "MANIFEST.sha256"
    manifest.write_text(ledger, encoding="utf-8")
    with zipfile.ZipFile(destination, "w", zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for path in sorted(files + [manifest]):
            name = ROOT.name + "/" + path.relative_to(ROOT).as_posix()
            entry = zipfile.ZipInfo(name, (2026, 11, 12, 0, 0, 0))
            entry.compress_type = zipfile.ZIP_DEFLATED
            entry.external_attr = 0o100644 << 16
            archive.writestr(entry, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(destination) as archive:
        bad = archive.testzip()
        if bad is not None:
            raise RuntimeError("ZIP checksum failure: " + bad)
        for line in ledger.splitlines():
            expected, relative = line.split("  ", 1)
            data = archive.read(ROOT.name + "/" + relative)
            if hashlib.sha256(data).hexdigest() != expected:
                raise RuntimeError("Manifest mismatch: " + relative)
        for required in ("ipra_smaller_envelope.tex",
                         "ipra_smaller_envelope.pdf",
                         "sections/finite_menu.tex", "reproduce.py"):
            archive.getinfo(ROOT.name + "/" + required)
    print(json.dumps({"archive": str(destination), "files": len(files) + 1,
                      "bytes": destination.stat().st_size,
                      "sha256": hashlib.sha256(destination.read_bytes()).hexdigest(),
                      "crc_and_manifest": "passed"}, indent=2))


if __name__ == "__main__":
    main()
