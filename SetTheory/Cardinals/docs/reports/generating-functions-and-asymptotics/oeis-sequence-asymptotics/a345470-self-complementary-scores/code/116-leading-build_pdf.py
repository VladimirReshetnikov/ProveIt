#!/usr/bin/env python3
"""Build report116.pdf deterministically without writing auxiliary files here."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
EPOCH = "1790899200"  # 2026-10-02 00:00:00 UTC

def build(output):
    engine = shutil.which("pdflatex")
    if engine is None:
        raise RuntimeError("pdflatex is required for PDF rebuilding")
    source = ROOT / "report116.tex"
    if not source.is_file():
        raise RuntimeError("report116.tex is missing")
    env = dict(os.environ, SOURCE_DATE_EPOCH=EPOCH, FORCE_SOURCE_DATE="1",
               TZ="UTC", LC_ALL="C", PYTHONDONTWRITEBYTECODE="1")
    with tempfile.TemporaryDirectory(prefix="score-report-build-") as temporary:
        work = Path(temporary)
        shutil.copyfile(source, work / source.name)
        # Debian installations may have the source packages but no prebuilt format.
        # Generate an isolated format rather than writing to a user/system cache.
        if Path("/usr/share/texlive/texmf-dist").is_dir():
            env["TEXMF"] = "{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
        env["TEXMFVAR"] = str(work / "texmf-var")
        env["TEXMFCONFIG"] = str(work / "texmf-config")
        env["TEXFORMATS"] = str(work) + "//:"
        formatter = shutil.which("pdftex")
        if formatter is None:
            raise RuntimeError("pdftex is required to generate the isolated format")
        result = subprocess.run(
            [formatter, "-ini", "-etex", "-no-shell-escape",
             "-interaction=nonstopmode", "-halt-on-error",
             "-jobname=pdflatex", "pdflatex.ini"],
            cwd=work, env=env, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, check=False)
        if result.returncode:
            raise RuntimeError("TeX format generation failed:\n" + result.stdout[-12000:])
        tex_input = (r"\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}"
                     r"\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}"
                     r"\input{report116.tex}")
        for _ in range(3):
            result = subprocess.run(
                [engine, "-no-shell-escape", "-interaction=nonstopmode",
                 "-halt-on-error", "-file-line-error", "-jobname=report116", tex_input],
                cwd=work, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, check=False)
            if result.returncode:
                raise RuntimeError("pdflatex failed:\n" + result.stdout[-12000:])
        log = (work / "report116.log").read_text(errors="replace")
        forbidden = ["Overfull \\hbox", "Overfull \\vbox",
                     "There were undefined references", "LaTeX Warning: Reference",
                     "LaTeX Warning: Citation", "Missing character:"]
        found = [item for item in forbidden if item in log]
        if found:
            lines = log.splitlines()
            details = "\n".join("\n".join(lines[max(0, i-1):i+4])
                                for i, line in enumerate(lines)
                                if any(item in line for item in forbidden))
            raise RuntimeError("PDF quality gate failed: " + ", ".join(found) + "\n" + details)
        output = Path(output).resolve()
        output.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(work / "report116.pdf", output)
    return output

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "report116.pdf")
    args = parser.parse_args()
    destination = build(args.output)
    print("Built " + str(destination))
