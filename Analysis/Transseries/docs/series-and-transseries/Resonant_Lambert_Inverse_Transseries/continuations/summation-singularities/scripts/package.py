#!/usr/bin/env python3
"""Package the article and reviewed supporting artifacts, excluding TeX auxiliaries."""
from pathlib import Path
import hashlib
import zipfile

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {".tex", ".pdf", ".png", ".py", ".json", ".md", ".txt"}


def main():
    files = sorted(p for p in ROOT.rglob("*")
                   if p.is_file() and (p.suffix in ALLOWED or p.name == "Makefile")
                   and p.name != "SHA256SUMS.txt"
                   and not any(part.startswith(".") for part in p.relative_to(ROOT).parts))
    required = ["polylogarithmic_reversion.pdf", "polylogarithmic_reversion.tex",
                "README.md", "CLAIMS.md", "PROVENANCE.json", "VALIDATION.md",
                "AUDIT_AND_INTEGRATION.md"]
    for name in required:
        if ROOT / name not in files:
            raise FileNotFoundError(name)
    manifest = ROOT / "SHA256SUMS.txt"
    manifest.write_text("".join(
        f"{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(ROOT).as_posix()}\n"
        for p in files), encoding="utf-8")
    files.append(manifest)
    destination = ROOT.parent / f"ProveIt_{ROOT.name}.zip"
    with zipfile.ZipFile(destination, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in sorted(files):
            archive.write(path, f"{ROOT.name}/{path.relative_to(ROOT).as_posix()}")
    with zipfile.ZipFile(destination) as archive:
        assert archive.testzip() is None
        assert len(archive.infolist()) == len(files)
    print(f"Created {destination}")
    print(f"{len(files)} files; {destination.stat().st_size} bytes; ZIP CRC checks passed.")


if __name__ == "__main__":
    main()
