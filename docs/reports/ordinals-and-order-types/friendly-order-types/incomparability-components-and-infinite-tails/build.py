"""Cross-platform LaTeX build with a BibTeX fallback. Python 3.9+."""
from pathlib import Path
import shutil
import subprocess
import sys


def main() -> int:
    root = Path(__file__).resolve().parent
    latex = shutil.which("pdflatex")
    bibtex = shutil.which("bibtex") or shutil.which("bibtex8") or shutil.which("bibtexu")
    if latex is None:
        print("pdflatex was not found. Install a LaTeX distribution with the newpx packages.",
              file=sys.stderr)
        return 2
    stem = "friendly_order_types"
    command = [latex, "-interaction=nonstopmode", "-halt-on-error", stem + ".tex"]
    try:
        subprocess.run(command, cwd=root, check=True)
        if bibtex is not None:
            subprocess.run([bibtex, stem], cwd=root, check=True)
        elif not (root / (stem + ".bbl")).exists():
            print("No BibTeX executable or prebuilt .bbl file was found.", file=sys.stderr)
            return 2
        else:
            print("BibTeX not found; using the included .bbl file.")
        subprocess.run(command, cwd=root, check=True)
        subprocess.run(command, cwd=root, check=True)
    except subprocess.CalledProcessError as error:
        print(f"Build failed with exit code {error.returncode}.", file=sys.stderr)
        return error.returncode
    print(root / (stem + ".pdf"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
