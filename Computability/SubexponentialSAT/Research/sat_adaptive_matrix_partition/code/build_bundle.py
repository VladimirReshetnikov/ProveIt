"""Build and check the research ZIP, excluding transient LaTeX/Python files."""
import hashlib
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
EXCLUDED_SUFFIXES = {".aux", ".log", ".out", ".toc", ".pyc"}


def selected_files():
    return sorted(p for p in ROOT.rglob("*")
                  if p.is_file() and "__pycache__" not in p.parts
                  and p.suffix not in EXCLUDED_SUFFIXES
                  and p.name not in {"MANIFEST.sha256", "build_transcript.txt"})


def main():
    if not (ROOT / "report.pdf").is_file():
        raise RuntimeError("compile the report first")
    files = selected_files()
    manifest = "".join(hashlib.sha256(p.read_bytes()).hexdigest() + "  " +
                       p.relative_to(ROOT).as_posix() + "\n" for p in files)
    (ROOT / "MANIFEST.sha256").write_text(manifest)
    files.append(ROOT / "MANIFEST.sha256")
    archive = ROOT.parent / (ROOT.name + ".zip")
    with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for p in sorted(files):
            name = ROOT.name + "/" + p.relative_to(ROOT).as_posix()
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 26, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            z.writestr(info, p.read_bytes(), compress_type=zipfile.ZIP_DEFLATED,
                       compresslevel=9)
    with zipfile.ZipFile(archive) as z:
        if z.testzip() is not None:
            raise RuntimeError("archive CRC check failed")
        for p in files:
            name = ROOT.name + "/" + p.relative_to(ROOT).as_posix()
            if z.read(name) != p.read_bytes():
                raise RuntimeError("archive member differs: " + name)
    print(f"Created {archive.name}: {len(files)} files, {archive.stat().st_size} bytes")
    print("SHA256 " + hashlib.sha256(archive.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
