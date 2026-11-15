#!/usr/bin/env python3
"""Compile the report, using a local TeX format/map if the installation needs it.

This script changes only the archive's own build directory and output PDF.
Python standard library and an installed TeX distribution are required.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent.parent
STEM = "zeta_functional_equation_ipra"
BUILD = ROOT / "build"
RUNTIME = BUILD / "texruntime"


def kpse(name: str) -> str:
    proc = subprocess.run(["kpsewhich", name], text=True, capture_output=True)
    return proc.stdout.strip() if proc.returncode == 0 else ""


def run_logged(args: list[str], name: str, *, cwd: Path, env: dict) -> None:
    proc = subprocess.run(args, cwd=cwd, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (BUILD / name).write_text(proc.stdout, encoding="utf-8")
    if proc.returncode:
        raise RuntimeError(
            f"{args[0]} failed; see {BUILD / name}\n{proc.stdout[-2500:]}"
        )


def main() -> None:
    for binary in ["pdflatex", "pdftex", "kpsewhich"]:
        if not shutil.which(binary):
            raise SystemExit(f"Required TeX executable not installed: {binary}")
    RUNTIME.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    fmt = kpse("pdflatex.fmt")
    generated_format = not bool(fmt)
    if generated_format:
        run_logged(
            ["pdftex", "-ini", "-etex", "-interaction=nonstopmode",
             "-halt-on-error", "-jobname=pdflatex", "-progname=pdflatex",
             "pdflatex.ini"],
            "format_build.log", cwd=RUNTIME, env=env,
        )
        fmt = str(RUNTIME / "pdflatex.fmt")
    generated_map = not bool(kpse("pdftex.map"))
    if generated_map:
        maps = []
        for name in ["lm.map", "symbols.map", "cm.map", "cmextra.map",
                     "latxfont.map"]:
            source = kpse(name)
            if source:
                maps.append(Path(source).read_text(encoding="utf-8"))
        if not maps:
            raise SystemExit("No installed scalable font maps were found.")
        (RUNTIME / "pdftex.map").write_text("\n".join(maps), encoding="utf-8")
        env["TEXFONTMAPS"] = str(RUNTIME) + "//:" + env.get("TEXFONTMAPS", "")
    args = ["pdflatex", f"-fmt={fmt}", "-interaction=nonstopmode",
            "-halt-on-error", f"-output-directory={BUILD}", f"{STEM}.tex"]
    for i in range(1, 4):
        run_logged(args, f"document_pass_{i}.log", cwd=ROOT, env=env)
    log = (BUILD / f"{STEM}.log").read_text(encoding="utf-8")
    overfull = re.findall(r"Overfull \\[hv]box .*", log)
    unresolved = (
        "There were undefined references" in log
        or bool(re.search(r"LaTeX Warning: (Reference|Citation).*undefined", log))
    )
    shutil.copy2(BUILD / f"{STEM}.pdf", ROOT / f"{STEM}.pdf")
    page_match = re.search(r"Output written on .*?\((\d+) pages?", log, re.S)
    summary = {
        "pdf": f"{STEM}.pdf",
        "passes": 3,
        "pdf_pages": int(page_match.group(1)) if page_match else None,
        "generated_local_format": generated_format,
        "generated_local_font_map": generated_map,
        "overfull_boxes": overfull,
        "unresolved_references": unresolved,
        "lean_status": "Uncompiled interface drafts; no full formalization.",
    }
    (ROOT / "provenance" / "build_validation.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, indent=2))
    if overfull or unresolved:
        raise SystemExit("PDF compiled, but layout/reference checks need attention.")


if __name__ == "__main__":
    main()
