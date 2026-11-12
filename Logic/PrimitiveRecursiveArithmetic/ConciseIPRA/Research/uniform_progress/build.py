"""Assemble the standalone LaTeX source and compile the research report."""
from pathlib import Path
import argparse
import re
import subprocess

ROOT = Path(__file__).resolve().parent
NAME = "ipra_uniform_progress"


def expand(text):
    def include(match):
        path = ROOT / match.group(1)
        if not path.suffix:
            path = path.with_suffix(".tex")
        return "% BEGIN " + str(path.relative_to(ROOT)) + "\n" + expand(path.read_text()) + "\n% END INCLUDE\n"
    text = re.sub(r"\\input\{([^}]+)\}", include, text)
    def listing(match):
        options = match.group(1) or ""
        return "\\begin{lstlisting}" + options + "\n" + (ROOT / match.group(2)).read_text().rstrip() + "\n\\end{lstlisting}"
    return re.sub(r"\\lstinputlisting(\[[^]]*\])?\{([^}]+)\}", listing, text)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-only", action="store_true")
    args = parser.parse_args()
    source = ROOT / (NAME + ".tex")
    source.write_text(expand((ROOT / "report.tex").read_text()))
    if args.source_only:
        return
    for _ in range(3):
        result = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", source.name],
                                cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode:
            print(result.stdout[-14000:])
            raise SystemExit(result.returncode)
    print(ROOT / (NAME + ".pdf"))


if __name__ == "__main__":
    main()
