#!/usr/bin/env python3
"""Build paper.pdf with installed TeX Live, creating local support if needed.

On an ordinary TeX Live installation `latexmk -pdf paper.tex` is sufficient.
This helper also handles environments with installed TeX/font sources but
without generated pdflatex.fmt or pdftex.map.  It changes no global config.
"""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]

def locate(name):
    p = subprocess.run(["kpsewhich", name], text=True, capture_output=True)
    return p.stdout.strip() if p.returncode == 0 else ""

if not shutil.which("pdflatex"):
    raise SystemExit("Install TeX Live with pdflatex, lmodern, AMS, and latex-extra packages.")

with tempfile.TemporaryDirectory(prefix="dirichlet_transport_tex_") as d:
    tmp = Path(d)
    env = os.environ.copy()
    cmd = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error"]
    if not locate("pdflatex.fmt"):
        process = subprocess.run(
            ["pdftex", "-etex", "-ini", "-jobname=pdflatex", "-progname=pdflatex",
             "-interaction=nonstopmode", "pdflatex.ini"],
            cwd=tmp, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (tmp / "format_build.txt").write_text(process.stdout)
        if process.returncode:
            print(process.stdout)
            raise SystemExit("Local pdfLaTeX format creation failed.")
        cmd.insert(1, "-fmt=" + str(tmp / "pdflatex.fmt"))
    if not locate("pdftex.map"):
        maps = []
        for name in ["lm.map", "cm.map", "cmextra.map", "symbols.map", "latxfont.map", "euler.map"]:
            p = locate(name)
            if p:
                maps.append(Path(p).read_text())
        (tmp / "pdftex.map").write_text("\n".join(maps))
        env["TEXFONTMAPS"] = str(tmp) + "//:" + env.get("TEXFONTMAPS", "")
    logs = []
    for iteration in range(3):
        p = subprocess.run(cmd + ["paper.tex"], cwd=ROOT, env=env,
                           text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        logs.append(p.stdout)
        if p.returncode:
            print(p.stdout)
            raise SystemExit("pdfLaTeX failed on pass " + str(iteration + 1))
    dest = ROOT / "data" / "pdf_build.txt"
    dest.write_text("\n\n".join(logs))
    print("Built", ROOT / "paper.pdf")
    print("Build log:", dest)
