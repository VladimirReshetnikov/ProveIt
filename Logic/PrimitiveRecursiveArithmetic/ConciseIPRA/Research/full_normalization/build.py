"""Assemble a standalone LaTeX source and compile its PDF."""
import argparse
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def assemble(path):
    text = path.read_text()
    text = re.sub(r"\\input\{([^}]+)\}",
                  lambda match: assemble(ROOT / match[1]), text)
    text = re.sub(r"\\lstinputlisting\{([^}]+)\}",
                  lambda match: "\\begin{lstlisting}\n"
                  + (ROOT / match[1]).read_text()
                  + "\\end{lstlisting}", text)
    return text


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tex-only", action="store_true")
    args = parser.parse_args()
    (ROOT / "report.tex").write_text(assemble(ROOT / "main.tex"))
    if args.tex_only:
        return
    target = ROOT / "build"
    target.mkdir(exist_ok=True)
    for run in range(3):
        result = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
             "-output-directory=build", "report.tex"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True)
        (target / f"pass-{run + 1}.txt").write_text(result.stdout)
        if result.returncode:
            print(result.stdout[-8000:])
            raise SystemExit(result.returncode)
    shutil.copy2(target / "report.pdf", ROOT / "report.pdf")
    print("Built report.tex and report.pdf")


if __name__ == "__main__":
    main()
