#!/usr/bin/env python3
"""Build the LaTeX report; use a private format if system formats are absent.

Only installed TeX files are used. Shell escape and shell command execution
are disabled. Generated build logs are retained under verification/.
"""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"
RECORDS = ROOT / "verification"


def run(command, environment, directory, record):
    with record.open("w", encoding="utf-8") as stream:
        result = subprocess.run(command, cwd=directory, env=environment,
                                stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        print("\n".join(record.read_text(errors="replace").splitlines()[-70:]))
        raise SystemExit(result.returncode)


def main():
    executable = shutil.which("pdflatex")
    if not executable:
        raise SystemExit("Install a LaTeX distribution with pdflatex.")
    RECORDS.mkdir(exist_ok=True)
    environment = dict(os.environ)
    roots = [Path("/usr/share/texlive/texmf-dist"), Path("/usr/share/texmf")]
    probe = subprocess.run(["kpsewhich", "pdflatex.fmt"],
                           capture_output=True, text=True)
    with tempfile.TemporaryDirectory(prefix="siegel-tex-") as temp:
        runtime = Path(temp)
        command = [executable]
        if probe.returncode and roots[0].is_dir():
            for variable, suffix in [
                ("TEXINPUTS", "tex"), ("TFMFONTS", "fonts/tfm"),
                ("T1FONTS", "fonts/type1"), ("ENCFONTS", "fonts/enc")
            ]:
                environment[variable] = ".:" + ":".join(
                    str(p / suffix) + "//" for p in roots) + ":"
            environment["TEXFONTMAPS"] = str(runtime) + ":" + ":".join(
                str(p / "fonts/map") + "//" for p in roots) + ":"
            environment["TEXFORMATS"] = str(runtime)
            environment["MKTEXFMT"] = "0"
            (runtime / "language.dat").write_text("english hyphen.tex\n")
            maps = []
            for rel in ["fonts/map/dvips/lm/lm.map",
                        "fonts/map/dvips/amsfonts/cm.map",
                        "fonts/map/dvips/amsfonts/cmextra.map",
                        "fonts/map/dvips/amsfonts/symbols.map",
                        "fonts/map/dvips/amsfonts/latxfont.map"]:
                for p in roots:
                    if (p / rel).is_file():
                        maps.append((p / rel).read_text())
                        break
            (runtime / "pdftex.map").write_text("\n".join(maps))
            ini = roots[0] / "tex/latex/tex-ini-files/pdflatex.ini"
            run(["pdftex", "-ini", "-etex", "-progname=pdflatex",
                 "-jobname=pdflatex", "-interaction=nonstopmode",
                 "-halt-on-error", "-no-shell-escape", str(ini)],
                environment, runtime, RECORDS / "tex_format.txt")
            command = ["pdftex", "-fmt=pdflatex", "-progname=pdflatex"]
        for i in range(1, 4):
            run(command + ["-interaction=nonstopmode", "-halt-on-error",
                           "-no-shell-escape", "siegel_ipra.tex"],
                environment, PAPER, RECORDS / f"tex_pass_{i}.txt")
            print(f"LaTeX pass {i} succeeded")
    print(PAPER / "siegel_ipra.pdf")


if __name__ == "__main__":
    main()
