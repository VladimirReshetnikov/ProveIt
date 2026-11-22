#!/usr/bin/env python3
"""Build a local pdfLaTeX format from an installed, incompletely configured TeX.

Normal TeX Live installations do not need this helper.  It was used because
the execution image had all TeX sources/fonts but missing /var/lib/texmf
generated files.  No system files are modified and no download is performed.
The JSON output gives the environment needed by a subsequent pdflatex call.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--texmf-dist", type=Path,
                        default=Path("/usr/share/texlive/texmf-dist"))
    parser.add_argument("--extra-texmf", type=Path,
                        default=Path("/usr/share/texmf"))
    args = parser.parse_args()
    base = args.destination.resolve()
    dist = args.texmf_dist.resolve()
    extra = args.extra_texmf.resolve()
    if not (dist / "tex/latex/base/latex.ltx").is_file():
        raise SystemExit("An installed LaTeX source tree is required.")
    for sub in ["tex/generic/config", "web2c/pdftex", "fonts/map/pdftex/local"]:
        (base / sub).mkdir(parents=True, exist_ok=True)
    language = dist / "tex/generic/config/language.us"
    (base / "tex/generic/config/language.dat").write_bytes(language.read_bytes())
    maps = [extra / "fonts/map/dvips/lm/lm.map"]
    maps += sorted((dist / "fonts/map/dvips/amsfonts").glob("*.map"))
    lines = []
    seen = set()
    for source in maps:
        for line in source.read_text().splitlines():
            if line not in seen:
                seen.add(line)
                lines.append(line)
    (base / "fonts/map/pdftex/local/pdftex.map").write_text("\n".join(lines) + "\n")
    changes = {"TEXMF": "{" + ",".join(map(str, [base, dist, extra])) + "}",
               "TEXMFVAR": str(base)}
    environment = dict(os.environ, **changes)
    command = ["pdftex", "-ini", "-etex", "-interaction=nonstopmode",
               "-halt-on-error", "-jobname=pdflatex", "-progname=pdflatex",
               "pdflatex.ini"]
    process = subprocess.run(command, cwd=base / "web2c/pdftex", env=environment,
                             text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT)
    (base / "format-build.txt").write_text(process.stdout)
    if process.returncode:
        raise SystemExit("Format build failed; inspect " + str(base / "format-build.txt"))
    print(json.dumps({"status": "local format built", "environment": changes,
                      "format": str(base / "web2c/pdftex/pdflatex.fmt")}, indent=2))


if __name__ == "__main__":
    main()
