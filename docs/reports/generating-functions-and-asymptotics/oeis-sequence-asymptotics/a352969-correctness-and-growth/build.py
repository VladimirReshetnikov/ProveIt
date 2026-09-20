#!/usr/bin/env python3
"""Build article.pdf with latexmk or pdflatex, keeping auxiliaries temporary."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def main() -> int:
    root = Path(__file__).resolve().parent
    source = root / "article.tex"
    if not source.is_file():
        print(f"Missing source: {source}", file=sys.stderr)
        return 1
    latexmk = shutil.which("latexmk")
    pdflatex = shutil.which("pdflatex")
    if latexmk is None and pdflatex is None:
        print("Install a TeX distribution containing pdflatex (for example, "
              "TeX Live or MiKTeX), then run this script again.", file=sys.stderr)
        return 1
    with tempfile.TemporaryDirectory(prefix="a352969-tex-") as work:
        if latexmk:
            commands = [[latexmk, "-pdf", f"-outdir={work}",
                         "-interaction=nonstopmode", "-halt-on-error", "article.tex"]]
        else:
            command = [pdflatex, f"-output-directory={work}",
                       "-interaction=nonstopmode", "-halt-on-error", "article.tex"]
            commands = [command] * 3  # Resolve references and the contents page.
        log = []
        for command in commands:
            result = subprocess.run(command, cwd=root, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True,
                                    errors="replace", check=False)
            log.append(result.stdout)
            if result.returncode:
                (root / "verification").mkdir(exist_ok=True)
                (root / "verification" / "latex-build.txt").write_text(
                    "\n".join(log), encoding="utf-8")
                print(result.stdout, file=sys.stderr)
                return result.returncode
        pdf = Path(work) / "article.pdf"
        if not pdf.is_file() or not pdf.read_bytes().startswith(b"%PDF-"):
            print("The TeX run did not produce a PDF.", file=sys.stderr)
            return 1
        shutil.copy2(pdf, root / "article.pdf")
        (root / "verification").mkdir(exist_ok=True)
        (root / "verification" / "latex-build.txt").write_text(
            "\n".join(log), encoding="utf-8")
    print(f"Built {root / 'article.pdf'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
