"""Rebuild the report with pdfLaTeX. No network access is required."""
from pathlib import Path
import os
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
engine = shutil.which("pdflatex")
if engine is None:
    raise SystemExit("Install a TeX distribution with pdfLaTeX to rebuild the PDF.")
env = os.environ.copy()
build = ROOT / "build"
build.mkdir(exist_ok=True)
# Some minimal Debian images contain the TeX trees without generated ls-R
# databases. Fall back to filesystem lookup, scoped to this child process.
lookup = subprocess.run(["kpsewhich", "pdflatex.ini"], capture_output=True, text=True)
if not lookup.stdout.strip() and Path("/usr/share/texlive/texmf-dist").exists():
    env["TEXMF"] = "{.,/etc/texmf,/usr/share/texmf,/usr/share/texlive/texmf-dist}"
lookup = subprocess.run(["kpsewhich", "pdftex.map"], env=env,
                        capture_output=True, text=True)
if not lookup.stdout.strip():
    # Generate only a local map from installed, unchanged font maps.
    maps = []
    for name in ["lm.map", "cm.map", "cmextra.map", "symbols.map", "latxfont.map"]:
        location = subprocess.run(["kpsewhich", name], env=env,
                                  capture_output=True, text=True).stdout.strip()
        if location:
            maps.append(Path(location).read_text())
    if maps:
        (build / "pdftex.map").write_text("\n".join(maps))
        env["TEXFONTMAPS"] = str(build) + "//:" + env.get("TEXFONTMAPS", "")
extra = []
lookup = subprocess.run(["kpsewhich", "pdflatex.fmt"], env=env,
                        capture_output=True, text=True)
if not lookup.stdout.strip():
    fmt = build / "pdflatex.fmt"
    if not fmt.exists():
        result = subprocess.run(
            ["pdftex", "-ini", "-etex", "-interaction=nonstopmode",
             "-halt-on-error", "-jobname=pdflatex", "-progname=pdflatex",
             "-output-directory=" + str(build), "pdflatex.ini"],
            cwd=ROOT, env=env, capture_output=True, text=True,
        )
        if result.returncode:
            print(result.stdout[-12000:])
            raise SystemExit(result.returncode)
    extra = ["-fmt=" + str(fmt)]
for _ in range(3):
    result = subprocess.run(
        [engine, *extra, "-interaction=nonstopmode", "-halt-on-error",
         "-output-directory=" + str(build), "ipra_502_scope_audit.tex"],
        cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
    )
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
shutil.copyfile(build / "ipra_502_scope_audit.pdf", ROOT / "ipra_502_scope_audit.pdf")
print("Built ipra_502_scope_audit.pdf")
