#!/usr/bin/env python3
"""Create the deterministic research ZIP and its SHA-256 manifest."""
from pathlib import Path
import hashlib
import zipfile

ROOT = Path(__file__).resolve().parent
NAME = "ProveIt_Lattice_Contacts_and_Mixed_Zeta_Identities_2026-10-11"
STEM = "Lattice_Contacts_and_Mixed_Zeta_Identities"


def deliverable_files():
    names = [
        "README.md", "INTEGRATION.md", "VALIDATION.md",
        "build.py", "run_checks.py", "package.py", "requirements.txt",
        "article.tex", "preamble.tex", "references.tex",
        STEM + ".tex", STEM + ".pdf", "build/latex.log",
    ]
    files = [ROOT / n for n in names]
    for folder in ["sections", "verification", "results", "provenance"]:
        files += [p for p in (ROOT / folder).rglob("*")
                  if p.is_file() and "__pycache__" not in p.parts
                  and p.suffix != ".pyc"]
    if any(not p.is_file() for p in files):
        raise FileNotFoundError("Build the article before packaging.")
    return sorted(files, key=lambda p: p.relative_to(ROOT).as_posix())


def main():
    files = deliverable_files()
    manifest = ROOT / "MANIFEST.sha256"
    manifest.write_text("".join(
        hashlib.sha256(p.read_bytes()).hexdigest()
        + "  " + p.relative_to(ROOT).as_posix() + "\n"
        for p in files), encoding="utf-8")
    files.append(manifest)
    target = ROOT.parent / (NAME + ".zip")
    with zipfile.ZipFile(target, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for p in sorted(files):
            info = zipfile.ZipInfo(NAME + "/" + p.relative_to(ROOT).as_posix(),
                                  date_time=(2026, 10, 11, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            z.writestr(info, p.read_bytes(), compress_type=zipfile.ZIP_DEFLATED,
                       compresslevel=9)
    with zipfile.ZipFile(target) as z:
        assert z.testzip() is None
        for line in manifest.read_text().splitlines():
            digest, name = line.split("  ", 1)
            assert hashlib.sha256(z.read(NAME + "/" + name)).hexdigest() == digest
    print(f"{target.name}: {len(files)} files, {target.stat().st_size} bytes")
    print("SHA-256: " + hashlib.sha256(target.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()

