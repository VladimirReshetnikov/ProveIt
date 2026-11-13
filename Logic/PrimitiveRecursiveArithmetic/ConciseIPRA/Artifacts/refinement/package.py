"""Rebuild the source manifest and deterministic research archive."""
from pathlib import Path
import hashlib
import zipfile


ROOT = Path(__file__).resolve().parent
EXCLUDED_SUFFIXES = {".aux", ".log", ".toc", ".out", ".pyc", ".synctex.gz"}


def deliverable_files():
    return sorted(
        path for path in ROOT.rglob("*")
        if path.is_file()
        and "__pycache__" not in path.parts
        and path.suffix not in EXCLUDED_SUFFIXES
        and not path.name.endswith(".synctex.gz")
        and path.name != "SHA256SUMS"
    )


def main():
    files = deliverable_files()
    for required in ("report.tex", "report.pdf", "README.txt"):
        if not (ROOT / required).is_file():
            raise SystemExit(f"Missing required deliverable: {required}")
    manifest = ROOT / "SHA256SUMS"
    manifest.write_text("".join(
        f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.relative_to(ROOT).as_posix()}\n"
        for path in files
    ), encoding="utf-8")
    archive = ROOT.with_suffix(".zip")
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as output:
        for path in sorted(files + [manifest]):
            name = f"{ROOT.name}/{path.relative_to(ROOT).as_posix()}"
            info = zipfile.ZipInfo(name, date_time=(2026, 11, 12, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            output.writestr(info, path.read_bytes(), compresslevel=9)
    with zipfile.ZipFile(archive) as check:
        damaged = check.testzip()
        if damaged is not None:
            raise SystemExit(f"Damaged archive member: {damaged}")
        for line in manifest.read_text(encoding="utf-8").splitlines():
            expected, name = line.split("  ", 1)
            content = check.read(f"{ROOT.name}/{name}")
            if hashlib.sha256(content).hexdigest() != expected:
                raise SystemExit(f"Archive hash mismatch: {name}")
    print(archive)
    print(f"{len(files) + 1} files; {archive.stat().st_size} bytes; archive integrity verified")


if __name__ == "__main__":
    main()
