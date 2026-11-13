"""Compile report.tex using installed TeX, without downloading dependencies.

Private format/font-map fallback adapted from the ProveIt
ipra_names_and_scopes build helper (MIT-0; upstream license included).
"""
from pathlib import Path
import os
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
env = os.environ.copy()


def locate(name):
    process = subprocess.run(["kpsewhich", name], env=env, text=True, capture_output=True)
    return process.stdout.strip()


if not locate("pdflatex.ini"):
    roots = [p for p in ("/usr/share/texmf", "/usr/share/texlive/texmf-dist")
             if Path(p).is_dir()]
    if roots:
        env["TEXMF"] = "{" + ",".join(roots) + "}"

log_path = ROOT / "evidence" / "pdf_build.log"
log_path.parent.mkdir(exist_ok=True)
with log_path.open("w") as log, tempfile.TemporaryDirectory(prefix="ipra-composition-") as directory:
    private = Path(directory)
    fmt = locate("pdflatex.fmt")
    if not fmt:
        subprocess.run(["pdftex", "-ini", "-etex", "-interaction=nonstopmode",
                        "-halt-on-error", "-jobname=pdflatex", "-progname=pdflatex",
                        "-output-directory=" + str(private), "pdflatex.ini"],
                       cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
        fmt = str(private / "pdflatex.fmt")
    if not locate("pdftex.map"):
        maps = []
        for name in ("cm.map", "cmextra.map", "latxfont.map", "symbols.map", "lm.map"):
            path = locate(name)
            if not path:
                raise SystemExit("Missing installed font map: " + name)
            maps.append(Path(path).read_text())
        (private / "pdftex.map").write_text("\n".join(maps))
        env["TEXFONTMAPS"] = str(private) + ":" + env.get("TEXFONTMAPS", "")
    for _ in range(3):
        subprocess.run(["pdftex", "-fmt=" + fmt, "-progname=pdflatex",
                        "-interaction=nonstopmode", "-halt-on-error", "report.tex"],
                       cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
print("Built report.pdf")
