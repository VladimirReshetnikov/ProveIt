#!/usr/bin/env python3
"""Build report.pdf without modifying an installed TeX distribution.

Normal TeX Live/MiKTeX installations use latexmk or pdflatex. A source-only
Debian TeX Live installation can use a temporary generated pdflatex format
and local font map. No format file is bundled with this report. Compilation
uses -no-shell-escape. The existing report.pdf is replaced only after success.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


BASE = Path(__file__).resolve().parents[1]


class BuildError(RuntimeError):
    pass


def run(command, cwd, env, log):
    print("Running:", " ".join(map(str, command)), flush=True)
    with log.open("w", encoding="utf-8") as stream:
        completed = subprocess.run(command, cwd=cwd, env=env,
                                   stdout=stream, stderr=subprocess.STDOUT)
    if completed.returncode:
        tail = "\n".join(log.read_text(errors="replace").splitlines()[-25:])
        raise BuildError(f"Command exited {completed.returncode}. Log: {log}\n{tail}")


def compile_report(stage, env, log_dir, prefix):
    latexmk = shutil.which("latexmk")
    pdflatex = shutil.which("pdflatex")
    if not pdflatex:
        raise BuildError("pdflatex is unavailable. Install a LaTeX distribution including "
                         "pdfTeX, the standard LaTeX packages, and Latin Modern fonts.")
    def tex_run(command, log):
        try:
            run(command, BASE, env, log)
        except BuildError as error:
            tex_log_path = stage / "report.log"
            if tex_log_path.is_file():
                lines = tex_log_path.read_text(errors="replace").splitlines()
                for index, line in enumerate(lines):
                    if line.startswith("!"):
                        detail = "\n".join(lines[index:index + 8])
                        raise BuildError(f"TeX diagnostic:\n{detail}\nFull TeX log: "
                                         f"{tex_log_path}\n{error}") from error
            raise
    if latexmk:
        tex_run([latexmk, "-pdf", "-g", "-interaction=nonstopmode", "-halt-on-error",
             "-pdflatex=pdflatex -no-shell-escape %O %S", f"-outdir={stage}",
             "report.tex"], log_dir / f"{prefix}-latexmk.log")
    else:
        # Inline bibliography: repeated pdflatex runs suffice; no BibTeX is needed.
        for number in range(1, 6):
            tex_run([pdflatex, "-no-shell-escape", "-interaction=nonstopmode",
                 "-halt-on-error", f"-output-directory={stage}", "report.tex"],
                log_dir / f"{prefix}-pdflatex-{number}.log")
            tex_log = (stage / "report.log").read_text(errors="replace")
            rerun = re.search(r"Rerun to get|Label\(s\) may have changed|rerunfilecheck.*Warning",
                              tex_log, re.IGNORECASE)
            if number >= 2 and not rerun:
                break
        else:
            raise BuildError("Cross-references still request a rerun after five pdflatex passes; "
                             f"inspect {stage / 'report.log'}.")
    pdf = stage / "report.pdf"
    if not pdf.is_file() or pdf.stat().st_size < 100:
        raise BuildError("TeX reported success without producing a usable report.pdf.")
    return pdf


def fallback_environment(runtime, original):
    pdftex = shutil.which("pdftex")
    if not pdftex:
        raise BuildError("The fallback requires pdftex. Install a complete TeX distribution.")
    roots = [p for p in (Path("/usr/share/texlive/texmf-dist"), Path("/usr/share/texmf"))
             if p.is_dir()]
    if not roots:
        raise BuildError("No standard source-only TeX Live trees were found. Install the "
                         "pdflatex format and packages for your platform.")
    env = original.copy()
    env["TEXINPUTS"] = ".:" + ":".join(str(p / "tex") + "//" for p in roots) + ":"
    env["TEXFORMATS"] = str(runtime) + "//:"
    for variable, subdirectory in (("TFMFONTS", "tfm"), ("T1FONTS", "type1"),
                                  ("VFFONTS", "vf"), ("ENCFONTS", "enc")):
        env[variable] = ":".join(str(p / "fonts" / subdirectory) + "//"
                                 for p in roots) + ":"
    env["TEXFONTMAPS"] = str(runtime) + "//:" + ":".join(
        str(p / "fonts/map") + "//" for p in roots) + ":"
    maps = []
    for root in roots:
        lm_map = root / "fonts/map/dvips/lm/lm.map"
        if lm_map.is_file():
            maps.append(lm_map)
        maps.extend(sorted((root / "fonts/map/dvips/amsfonts").glob("*.map")))
    if not any(p.name == "lm.map" for p in maps):
        raise BuildError("The fallback requires Latin Modern fonts and their lm.map file.")
    (runtime / "pdftex.map").write_text(
        "\n".join(p.read_text(errors="strict") for p in maps), encoding="utf-8")
    return pdftex, env


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=BASE / "report.pdf",
                        help="destination PDF (default: report.pdf beside report.tex)")
    parser.add_argument("--log-dir", type=Path,
                        help="directory for compilation logs and auxiliary files")
    args = parser.parse_args()
    if not (BASE / "report.tex").is_file():
        raise BuildError(f"Missing main document: {BASE / 'report.tex'}")
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    log_dir = (args.log_dir or BASE / "validation/replay" / f"pdf-{stamp}").resolve()
    log_dir.mkdir(parents=True, exist_ok=True)
    stage = log_dir / "build"
    stage.mkdir(exist_ok=True)
    env = os.environ.copy()
    env.setdefault("SOURCE_DATE_EPOCH", str(int(
        datetime(2026, 11, 25, 20, 45, 4, tzinfo=timezone.utc).timestamp())))
    try:
        pdf = compile_report(stage, env, log_dir, "normal")
    except BuildError as first_error:
        logs = "\n".join(p.read_text(errors="replace") for p in log_dir.glob("normal-*.log"))
        missing_format = ("can't find the format file" in logs or
                          "I can't find the format" in logs or
                          "pdflatex.fmt" in logs and "not found" in logs)
        if not missing_format:
            raise
        print("Normal build lacks a pdflatex format; generating a temporary local format.",
              flush=True)
        with tempfile.TemporaryDirectory(prefix="grh-synthesis-tex-") as temporary:
            runtime = Path(temporary)
            pdftex, fallback_env = fallback_environment(runtime, env)
            run([pdftex, "-ini", "-etex", "-no-shell-escape", "-interaction=nonstopmode",
                 "-halt-on-error", "-jobname=pdflatex", "*pdflatex.ini"],
                runtime, fallback_env, log_dir / "fallback-format.log")
            try:
                pdf = compile_report(stage, fallback_env, log_dir, "fallback")
            except BuildError as fallback_error:
                raise BuildError(f"Temporary-format build failed. {fallback_error}") from first_error
    destination = args.output.resolve()
    destination.parent.mkdir(parents=True, exist_ok=True)
    # Atomic replacement leaves an existing reviewed PDF intact after a failed build.
    with tempfile.NamedTemporaryFile(prefix=destination.stem + "-", suffix=".pdf",
                                     dir=destination.parent, delete=False) as stream:
        pending = Path(stream.name)
    try:
        shutil.copyfile(pdf, pending)
        os.replace(pending, destination)
    finally:
        pending.unlink(missing_ok=True)
    print(f"Built {destination}\nCompilation logs: {log_dir}")


if __name__ == "__main__":
    try:
        main()
    except (BuildError, OSError, subprocess.SubprocessError) as error:
        print(f"PDF BUILD FAILED: {error}", file=sys.stderr)
        sys.exit(1)
