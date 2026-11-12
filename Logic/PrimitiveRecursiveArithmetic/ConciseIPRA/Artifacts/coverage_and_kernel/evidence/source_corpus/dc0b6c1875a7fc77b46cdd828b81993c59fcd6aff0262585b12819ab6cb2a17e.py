"""Compile the modular or standalone report with pdfLaTeX, without shell escape.

Use --standalone to compile the fully expanded source. A private fallback
repairs missing format/font-map caches when the installed TeX sources exist.
"""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def lookup(name, env):
    probe = subprocess.run(["kpsewhich", name], env=env, capture_output=True, text=True)
    return probe.stdout.strip() if probe.returncode == 0 else ""


def build(standalone=False):
    if not shutil.which("pdflatex"):
        raise SystemExit("Install a LaTeX distribution with pdfLaTeX and the packages in report.tex.")
    name = "report_standalone.tex" if standalone else "report.tex"
    env = os.environ.copy()
    with tempfile.TemporaryDirectory(prefix="ipra-tex-") as directory:
        work = Path(directory)
        if not lookup("article.cls", env):
            texroot = Path("/usr/share/texlive/texmf-dist")
            if not (texroot / "tex/latex/base/article.cls").exists():
                raise SystemExit("The installed TeX distribution lacks article.cls.")
            env["TEXMF"] = "{.,/usr/share/texlive/texmf-dist,/usr/share/texmf,/etc/texmf}"
        if not lookup("pdflatex.fmt", env):
            subprocess.run(["pdftex", "-ini", "-etex", "-jobname=pdflatex",
                            "-progname=pdflatex", "pdflatex.ini"], cwd=work,
                           env=env, check=True, stdout=subprocess.DEVNULL)
            env["TEXFORMATS"] = str(work) + os.pathsep
        if not lookup("pdftex.map", env):
            maps = [Path("/usr/share/texmf/fonts/map/dvips/lm/lm.map")]
            maps += sorted(Path("/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts").glob("*.map"))
            if not all(path.exists() for path in maps):
                raise SystemExit("Missing Latin Modern/AMS font maps; repair the TeX installation.")
            (work / "pdftex.map").write_text("\n".join(path.read_text() for path in maps) + "\n")
            env["TEXFONTMAPS"] = str(work) + os.pathsep
        for _ in range(3):
            result = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", name],
                                    cwd=ROOT, env=env, capture_output=True, text=True)
            if result.returncode:
                print(result.stdout)
                raise SystemExit(result.returncode)
        print("Built " + str(ROOT / Path(name).with_suffix(".pdf")))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--standalone", action="store_true")
    build(parser.parse_args().standalone)
