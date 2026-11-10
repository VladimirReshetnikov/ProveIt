"""Build the report locally, with shell escape disabled and no downloads.

The optional local TeX-format fallback is adapted from the attributed
ipra_unclamped_feedback_2026-11-09 build helper in the source corpus.
"""
from pathlib import Path
import json
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent


def environment(work):
    env = dict(os.environ, SOURCE_DATE_EPOCH="1794268800", FORCE_SOURCE_DATE="1")
    probe = subprocess.run(["kpsewhich", "pdflatex.fmt"], env=env,
                           capture_output=True, text=True)
    if probe.returncode == 0 and probe.stdout.strip():
        return env
    trees = [Path("/usr/share/texmf"), Path("/usr/share/texlive/texmf-dist")]
    if not all(p.is_dir() for p in trees):
        raise SystemExit("An installed pdfLaTeX format is required.")
    cache = work / "texcache"
    cache.mkdir(exist_ok=True)
    env["TEXMF"] = "{" + ",".join(map(str, [cache, *trees])) + "}"
    target = cache / "web2c/pdftex/pdflatex.fmt"
    if not target.exists():
        target.parent.mkdir(parents=True, exist_ok=True)
        result = subprocess.run(
            ["pdftex", "-ini", "-etex", "-no-shell-escape",
             "-interaction=nonstopmode", "-halt-on-error", "-jobname=pdflatex",
             "-progname=pdflatex", "pdflatex.ini"],
            cwd=cache, env=env, capture_output=True, text=True)
        if result.returncode:
            raise SystemExit(result.stdout[-9000:] + result.stderr)
        shutil.move(cache / "pdflatex.fmt", target)
    maps = [trees[0] / "fonts/map/dvips/lm/lm.map"]
    maps.extend(sorted((trees[1] / "fonts/map/dvips/amsfonts").glob("*.map")))
    fontmap = cache / "fonts/map/pdftex/local/pdftex.map"
    fontmap.parent.mkdir(parents=True, exist_ok=True)
    fontmap.write_text("\n".join(p.read_text() for p in maps))
    return env


def main():
    work = ROOT / "build"
    work.mkdir(exist_ok=True)
    env = environment(work)
    source = (ROOT / "report.tex").read_text()
    source = source.replace(r"\input{compiler_appendix.tex}",
                            (ROOT / "compiler_appendix.tex").read_text())
    (ROOT / "report_standalone.tex").write_text(source)
    for _ in range(3):
        result = subprocess.run(
            ["pdflatex", "-no-shell-escape", "-interaction=nonstopmode",
             "-halt-on-error", "-output-directory=" + str(work), "report.tex"],
            cwd=ROOT, env=env, capture_output=True, text=True)
        (work / "last_build_stdout.txt").write_text(result.stdout + result.stderr)
        if result.returncode:
            raise SystemExit(result.stdout[-10000:] + result.stderr)
    shutil.copyfile(work / "report.pdf", ROOT / "report.pdf")
    log = (work / "report.log").read_text()
    warnings = [line for line in log.splitlines()
                if "Overfull" in line or "undefined" in line or "Warning:" in line]
    (ROOT / "evidence/build.json").write_text(json.dumps({
        "passes": 3, "shell_escape": False, "warnings": warnings,
        "page_report": re.findall(r"Output written on.*", log),
        "pdf_bytes": (ROOT / "report.pdf").stat().st_size,
    }, indent=2) + "\n")
    print(json.dumps({"output": "report.pdf", "warnings": warnings}))


if __name__ == "__main__":
    main()
