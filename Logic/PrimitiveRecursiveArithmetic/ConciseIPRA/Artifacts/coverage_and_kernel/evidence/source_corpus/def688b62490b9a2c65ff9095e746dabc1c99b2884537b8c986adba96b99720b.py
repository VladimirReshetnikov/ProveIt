"""Expand the report to one TeX source and compile its PDF without a network."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
NAME = "ipra_three_schema_2026-11-09"


def prepare_tex_environment(environment, directory):
    """Local missing-format recovery, adapted from the supplied self-comparison build."""
    probe = subprocess.run(["kpsewhich", "pdflatex.fmt"], text=True, capture_output=True)
    if probe.stdout.strip():
        return False
    probe = subprocess.run(["kpsewhich", "-var-value=TEXMFDIST"],
                           text=True, capture_output=True, check=True)
    distribution = Path(probe.stdout.strip())
    if not (distribution / "tex/latex/base/latex.ltx").is_file():
        raise RuntimeError("A TeX distribution with LaTeX sources and report packages is required")
    roots = [p for p in (Path("/etc/texmf"), Path("/usr/share/texmf"), distribution) if p.is_dir()]
    environment["TEXMF"] = "{" + ",".join(["."] + [str(p) for p in roots]) + "}"
    run = subprocess.run(["pdftex", "-ini", "-etex", "-jobname=pdflatex", "-progname=pdflatex",
                          "-interaction=nonstopmode", "-halt-on-error", "pdflatex.ini"],
                         cwd=directory, env=environment, text=True, capture_output=True, timeout=120)
    if run.returncode:
        raise RuntimeError(run.stdout + run.stderr)
    maps = []
    for root in roots:
        lm = root / "fonts/map/dvips/lm/lm.map"
        if lm.is_file():
            maps.append(lm)
        maps.extend(sorted((root / "fonts/map/dvips/amsfonts").glob("*.map")))
    (directory / "pdftex.map").write_text("\n".join(p.read_text() for p in maps))
    environment["TEXFORMATS"] = str(directory) + ":"
    environment["TEXFONTMAPS"] = ":".join([str(directory) + "//"] +
                                           [str(p / "fonts/map") + "//" for p in roots]) + ":"
    return True


def expand(path):
    source = path.read_text()
    return re.sub(r"\\input\{([^}]+)\}",
                  lambda match: expand(ROOT / (match[1] + ".tex")), source)


def main():
    if not shutil.which("pdflatex"):
        raise RuntimeError("pdfLaTeX is required to rebuild the PDF")
    target = ROOT / (NAME + ".tex")
    target.write_text(expand(ROOT / "report.tex"))
    work = ROOT / "tmp" / "latex"
    work.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    fallback = prepare_tex_environment(environment, work)
    command = ["pdflatex", "-no-shell-escape", "-interaction=nonstopmode",
               "-halt-on-error", "-output-directory=" + str(work), str(target)]
    runs = []
    for _ in range(3):
        run = subprocess.run(command, cwd=ROOT, env=environment,
                             text=True, capture_output=True, timeout=120)
        runs.append({"exit_code": run.returncode})
        if run.returncode:
            print(run.stdout[-12000:])
            raise RuntimeError("pdfLaTeX failed")
    log = (work / (NAME + ".log")).read_text(errors="replace")
    warnings = [line for line in log.splitlines()
                if any(token in line for token in ("Overfull", "Underfull", "undefined", "Rerun to"))]
    shutil.copyfile(work / (NAME + ".pdf"), ROOT / (NAME + ".pdf"))
    (ROOT / "evidence/latex_final.log").write_text(log)
    receipt = {"runs": runs, "warnings": warnings, "local_format_fallback": fallback,
               "source_sha256": hashlib.sha256(target.read_bytes()).hexdigest(),
               "pdf_sha256": hashlib.sha256((ROOT / (NAME + ".pdf")).read_bytes()).hexdigest()}
    (ROOT / "evidence/build.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
