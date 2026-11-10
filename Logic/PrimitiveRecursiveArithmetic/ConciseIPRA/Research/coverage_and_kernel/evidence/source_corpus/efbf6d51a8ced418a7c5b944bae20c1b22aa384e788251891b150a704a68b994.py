"""Compile the complete report with an existing TeX installation."""
from pathlib import Path
import os
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
engine = shutil.which("pdflatex")
if not engine:
    raise SystemExit("pdflatex is required; install a TeX distribution first")
build = ROOT / "build"
build.mkdir(exist_ok=True)
env = os.environ.copy()


def locate(name):
    result = subprocess.run(["kpsewhich", name], env=env,
                            text=True, capture_output=True)
    return result.stdout.strip() if result.returncode == 0 else ""


# Some minimal images contain the packages but have empty filename databases.
# Use direct tree lookup only in that case; ordinary installations are unchanged.
if not locate("pdflatex.ini"):
    trees = [p for p in ("/usr/share/texlive/texmf-dist", "/usr/share/texmf")
             if Path(p).is_dir()]
    if trees:
        env["TEXMF"] = "{" + ",".join(trees) + "}"
cache = build / "tex-cache"
cache.mkdir(exist_ok=True)
if not locate("pdflatex.fmt"):
    if not locate("pdflatex.ini"):
        raise SystemExit("The installed TeX distribution lacks pdflatex.ini")
    result = subprocess.run(
        ["pdftex", "-ini", "-etex", "-jobname=pdflatex",
         "-progname=pdflatex", "pdflatex.ini"],
        cwd=cache, env=env, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, text=True)
    (cache / "format_output.txt").write_text(result.stdout)
    if result.returncode:
        print(result.stdout[-12000:])
        raise SystemExit(result.returncode)
    env["TEXFORMATS"] = str(cache) + os.pathsep + env.get("TEXFORMATS", "")
if not locate("pdftex.map"):
    maps = []
    for name in ("lm.map", "cm.map", "cmextra.map", "symbols.map",
                 "euler.map", "latxfont.map"):
        path = locate(name)
        if path:
            maps.append(Path(path).read_text())
    if not maps:
        raise SystemExit("Scalable Latin Modern and AMS font maps are required")
    (cache / "pdftex.map").write_text("\n".join(maps))
    env["TEXFONTMAPS"] = str(cache) + os.pathsep + env.get("TEXFONTMAPS", "")
for _ in range(3):
    result = subprocess.run(
        [engine, "-interaction=nonstopmode", "-halt-on-error",
         "-file-line-error", "-output-directory=" + str(build), "report.tex"],
        cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (build / "compiler_output.txt").write_text(result.stdout)
    if result.returncode:
        print(result.stdout[-12000:])
        raise SystemExit(result.returncode)
target = ROOT / "ipra_shared_continuation.pdf"
shutil.copyfile(build / "report.pdf", target)
print(target.name)
