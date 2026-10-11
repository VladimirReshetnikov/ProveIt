#!/usr/bin/env python3
"""Assemble the standalone TeX source and compile the research article."""
from __future__ import annotations

import argparse
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
STEM = "Exact_Resonance_and_Coordinate_Transport"


def assemble() -> Path:
    source = ROOT / f"{STEM}.tex"
    parts = [
        "% Standalone source, assembled from the supplied modular sections.\n"
        "% Regenerate after editing with: python3 build.py --assemble-only\n",
        (ROOT / "preamble.tex").read_text(encoding="utf-8"),
        "\n\\begin{document}\n",
    ]
    for path in sorted((ROOT / "sections").glob("*.tex")):
        parts.append(f"\n% BEGIN {path.relative_to(ROOT).as_posix()}\n")
        parts.append(path.read_text(encoding="utf-8"))
        parts.append(f"\n% END {path.relative_to(ROOT).as_posix()}\n")
    parts.extend([
        "\n% BEGIN references.tex\n",
        (ROOT / "references.tex").read_text(encoding="utf-8"),
        "\n\\end{document}\n",
    ])
    source.write_text("".join(parts), encoding="utf-8")
    return source


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assemble-only", action="store_true")
    parser.add_argument("--engine", default="lualatex",
                        choices=("lualatex", "pdflatex", "xelatex"))
    args = parser.parse_args()
    source = assemble()
    print(f"Assembled {source.name}", flush=True)
    if args.assemble_only:
        return
    executable = shutil.which(args.engine)
    if executable is None:
        raise SystemExit(f"TeX engine is unavailable: {args.engine}")
    build_dir = ROOT / ".build"
    build_dir.mkdir(exist_ok=True)
    command = [
        executable, "-interaction=nonstopmode", "-halt-on-error",
        "-file-line-error", f"-output-directory={build_dir}", source.name,
    ]
    for number in range(1, 4):
        print(f"TeX pass {number}/3", flush=True)
        result = subprocess.run(command, cwd=ROOT, text=True,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, check=False)
        (build_dir / f"pass-{number}.txt").write_text(
            result.stdout, encoding="utf-8")
        if result.returncode:
            print("\n".join(result.stdout.splitlines()[-80:]))
            raise SystemExit(result.returncode)
    destination = ROOT / f"{STEM}.pdf"
    shutil.copy2(build_dir / destination.name, destination)
    print(f"Compiled {destination.name}", flush=True)
    log_text = (build_dir / f"{STEM}.log").read_text(
        encoding="utf-8", errors="replace")
    problems = [line for line in log_text.splitlines()
                if any(token in line for token in (
                    "undefined", "Overfull", "Underfull",
                    "LaTeX Warning:", "Package hyperref Warning:"))]
    if problems:
        print("Typesetting diagnostics:")
        print("\n".join(problems))


if __name__ == "__main__":
    main()
