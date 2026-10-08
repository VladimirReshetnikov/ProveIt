"""Build the review archive and verify it compiles without workspace files.

The PDF must already be current. This command does not rerun benchmarks or
the test suite; it checks archive integrity and an independent clean TeX build.
"""
from pathlib import Path
import argparse
import json
import shutil
import subprocess
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
EXCLUDED_SUFFIXES = {".aux", ".toc", ".out", ".fls", ".fdb_latexmk", ".pyc"}


def included(path):
    relative = path.relative_to(ROOT)
    if "__pycache__" in relative.parts or ".pytest_cache" in relative.parts:
        return False
    if path.suffix in EXCLUDED_SUFFIXES:
        return False
    if relative == Path("article/main.log"):
        return False
    return path.is_file()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT.parent / "deliverables")
    args = parser.parse_args()
    destination = args.output.resolve()
    destination.mkdir(parents=True, exist_ok=True)
    if destination == ROOT or ROOT in destination.parents:
        raise ValueError("Archive destination must be outside the package tree.")
    files = sorted(p for p in ROOT.rglob("*") if included(p))
    required = [
        "article/main.tex", "article/main.pdf", "integration.patch",
        "results/full_validation.log", "results/article_qa.json",
        "fast/fastunknot/twist/tail.py",
        "fast/fastunknot/twist/streaming.py",
        "fast/fastunknot/braid_profile.py",
    ]
    for name in required:
        if ROOT / name not in files:
            raise ValueError("Missing required deliverable: " + name)
    archive = destination / "unknot_twist_research_2026-10-08.zip"
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as output:
        for path in files:
            relative = Path("unknot_twist_continuation") / path.relative_to(ROOT)
            info = zipfile.ZipInfo(relative.as_posix(), date_time=(2026, 10, 8, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = ((0o100755 if path.suffix == ".sh" else 0o100644) << 16)
            output.writestr(info, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED,
                            compresslevel=9)
    with zipfile.ZipFile(archive) as check:
        assert check.testzip() is None, "Archive CRC check failed."
        names = check.namelist()
        assert len(names) == len(set(names)) == len(files)
        assert not any(name.startswith("/") or ".." in Path(name).parts for name in names)
        with tempfile.TemporaryDirectory(prefix="unknot-release-check-") as temp:
            check.extractall(temp)
            article = Path(temp) / "unknot_twist_continuation" / "article"
            run = subprocess.run(
                ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
                cwd=article, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if run.returncode:
                raise RuntimeError("Clean archived-source build failed:\n" + run.stdout[-5000:])
            original_text = subprocess.check_output(
                ["pdftotext", "-layout", str(ROOT / "article/main.pdf"), "-"])
            rebuilt_text = subprocess.check_output(
                ["pdftotext", "-layout", str(article / "main.pdf"), "-"])
            assert original_text == rebuilt_text, "Clean rebuilt PDF text differs."
    pdf = destination / "unknot_twist_research_2026-10-08.pdf"
    shutil.copy2(ROOT / "article/main.pdf", pdf)
    print(json.dumps({
        "zip": str(archive), "pdf": str(pdf), "archive_files": len(files),
        "zip_bytes": archive.stat().st_size, "pdf_bytes": pdf.stat().st_size,
        "crc_check": "passed", "clean_tex_build": "passed",
        "rebuilt_pdf_text_matches": True,
    }, indent=2))


if __name__ == "__main__":
    main()
