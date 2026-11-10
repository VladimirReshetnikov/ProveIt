"""Compile the complete report with a standard TeX installation."""
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def flatten(path):
    text = path.read_text()
    text = re.sub(r"\\input\{([^}]+)\}",
                  lambda match: flatten(ROOT / match.group(1)), text)
    text = re.sub(r"\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}",
                  lambda match: "\\begin{lstlisting}" + (match.group(1) or "")
                  + "\n" + (ROOT / match.group(2)).read_text().rstrip()
                  + "\n\\end{lstlisting}", text)
    return text


def main():
    (ROOT / "standalone.tex").write_text(flatten(ROOT / "report.tex"))
    if shutil.which("latexmk"):
        command = ["latexmk", "-pdf", "-interaction=nonstopmode",
                   "-halt-on-error", "-file-line-error", "report.tex"]
        subprocess.run(command, cwd=ROOT, check=True)
    elif shutil.which("pdflatex"):
        for _ in range(3):
            subprocess.run(["pdflatex", "-interaction=nonstopmode",
                            "-halt-on-error", "-file-line-error", "report.tex"],
                           cwd=ROOT, check=True)
    else:
        raise SystemExit("Install TeX Live or MiKTeX with pdflatex to rebuild the PDF.")
    print(ROOT / "report.pdf")


if __name__ == "__main__":
    main()
