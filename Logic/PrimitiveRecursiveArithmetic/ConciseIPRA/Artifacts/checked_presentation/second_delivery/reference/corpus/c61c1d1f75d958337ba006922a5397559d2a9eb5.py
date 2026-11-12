"""Build a genuinely standalone TeX source, then optionally compile it."""
from pathlib import Path
import argparse
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
INPUT = re.compile(r"\\input\{([^}]+)\}")
LISTING = re.compile(r"\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}")


def expand(text):
    def include(match):
        path = ROOT / match.group(1)
        return "\n% BEGIN " + match.group(1) + "\n" + expand(
            path.read_text()) + "\n% END " + match.group(1) + "\n"

    text = INPUT.sub(include, text)

    def listing(match):
        options = match.group(1) or ""
        content = (ROOT / match.group(2)).read_text().rstrip()
        return "\\begin{lstlisting}" + options + "\n" + content + \
               "\n\\end{lstlisting}"

    return LISTING.sub(listing, text)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pdf", action="store_true")
    args = parser.parse_args()
    destination = ROOT / "ipra_single_binder.tex"
    destination.write_text(expand((ROOT / "sections/main.tex").read_text()))
    if args.pdf:
        subprocess.run(
            [sys.executable, str(ROOT / "build_pdf.py"),
             "--tex", str(destination),
             "--output", str(ROOT / "ipra_single_binder.pdf"),
             "--log", str(ROOT / "evidence/latex_build.txt")],
            cwd=ROOT, check=True,
        )
    print(destination.name)


if __name__ == "__main__":
    main()
