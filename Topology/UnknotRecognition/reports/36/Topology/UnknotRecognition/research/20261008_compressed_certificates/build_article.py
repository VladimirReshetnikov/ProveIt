"""Compile the article in a clean temporary directory and publish closed files.

Usage: python3 build_article.py [--render-dir /absolute/path/to/qa]
Requires latexmk, a standard TeX Live installation and Poppler's pdfinfo.
Optional page rendering uses pdftoppm. Existing source files are not altered.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ARTICLE = HERE / "article"
NAME = "unknot_compressed_certificates"


def atomic_write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".stage")
    with temporary.open("wb") as out:
        out.write(data)
        out.flush()
        os.fsync(out.fileno())
    os.replace(temporary, path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--render-dir", type=Path)
    args = parser.parse_args()
    sources = sorted(ARTICLE.glob("*.tex")) + sorted((ARTICLE / "figures").glob("*.pdf"))
    hashes = {p.relative_to(ARTICLE).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sources}
    with tempfile.TemporaryDirectory(prefix="proveit-article-") as directory:
        temporary = Path(directory)
        for source in ARTICLE.glob("*.tex"):
            shutil.copy2(source, temporary / source.name)
        shutil.copytree(ARTICLE / "figures", temporary / "figures")
        build = subprocess.run(["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
                                NAME + ".tex"], cwd=temporary, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
        if build.returncode:
            print(build.stdout)
            build.check_returncode()
        log = (temporary / (NAME + ".log")).read_bytes()
        forbidden = (b"Overfull", b"undefined", b"same identifier", b"LaTeX Warning",
                     b"Package amsmath Warning")
        if any(value in log for value in forbidden):
            raise RuntimeError("Review the LaTeX log: an overflow or reference warning remains")
        pdf = temporary / (NAME + ".pdf")
        info = subprocess.run(["pdfinfo", str(pdf)], text=True, capture_output=True, check=True).stdout
        pages = int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1))
        pdf_bytes = pdf.read_bytes()
        atomic_write(ARTICLE / pdf.name, pdf_bytes)
        atomic_write(HERE / "verification/latex_build.log", log)
        report = {"status": "COMPILED_AND_PARSED", "pages": pages,
                  "pdf_bytes": len(pdf_bytes), "pdf_sha256": hashlib.sha256(pdf_bytes).hexdigest(),
                  "source_sha256": hashes, "overflow_or_reference_warnings": 0}
        if args.render_dir:
            render = temporary / "render"
            render.mkdir()
            subprocess.run(["pdftoppm", "-r", "90", "-png", str(pdf), str(render / "page")],
                           check=True)
            images = sorted(render.glob("page-*.png"))
            if len(images) != pages:
                raise RuntimeError("Rendered page count does not match PDF")
            for source in images:
                atomic_write(args.render_dir.resolve() / source.name, source.read_bytes())
            report["rendered_pages"] = len(images)
        atomic_write(HERE / "verification/article_build.json",
                     (json.dumps(report, indent=2) + "\n").encode())
        print(json.dumps({key: value for key, value in report.items() if key != "source_sha256"},
                         indent=2))


if __name__ == "__main__":
    main()
