#!/usr/bin/env python3
"""Build the standalone LaTeX article without changing the release directory."""
from pathlib import Path
import argparse
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="destination PDF, preferably outside this release directory")
    args = parser.parse_args()
    if shutil.which("pdflatex") is None:
        raise SystemExit("pdflatex is required (standard TeX Live packages).")
    source = ROOT / "report/con-zfc-parity-norms.tex"
    destination = args.output.expanduser().resolve()
    with tempfile.TemporaryDirectory(prefix="con-zfc-parity-tex-") as tmp:
        work = Path(tmp)
        shutil.copy2(source, work / source.name)
        for _ in range(3):
            result = subprocess.run(
                ["pdflatex", "-no-shell-escape", "-interaction=nonstopmode",
                 "-halt-on-error", source.name],
                cwd=work, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
            )
            if result.returncode:
                raise SystemExit(result.stdout)
        log = (work / (source.stem + ".log")).read_text(errors="replace")
        if "undefined references" in log or "Overfull" in log:
            raise SystemExit("Review the TeX layout or references:\n" + log)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(work / (source.stem + ".pdf"), destination)
    print("Built " + str(destination))


if __name__ == "__main__":
    main()
