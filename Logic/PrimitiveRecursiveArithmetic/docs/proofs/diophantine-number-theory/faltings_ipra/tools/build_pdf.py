#!/usr/bin/env python3
"""Compile the report; use a private TeX format if system databases are absent."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
source = "faltings_ipra.tex"
normal = shutil.which("pdflatex")
if normal is None:
    raise SystemExit("Install a LaTeX distribution providing pdflatex.")


def execute(command, env, log_path, cwd):
    with log_path.open("w") as log:
        proc = subprocess.run(command, cwd=cwd, env=env, stdout=log,
                              stderr=subprocess.STDOUT)
    if proc.returncode:
        print("\n".join(log_path.read_text(errors="replace").splitlines()[-60:]))
        raise SystemExit(proc.returncode)


def main():
    env = dict(os.environ)
    verification = root / "verification"
    verification.mkdir(exist_ok=True)
    roots = [Path("/usr/share/texlive/texmf-dist"), Path("/usr/share/texmf")]
    check = subprocess.run(["kpsewhich", "pdflatex.fmt"], capture_output=True,
                            text=True) if shutil.which("kpsewhich") else None
    with tempfile.TemporaryDirectory(prefix="faltings-tex-") as tmp:
        runtime = Path(tmp)
        command = [normal]
        if check is not None and check.returncode != 0 and roots[0].is_dir():
            env.update({
                "TEXINPUTS": ".:" + ":".join(str(p/"tex")+"//" for p in roots)+":",
                "TFMFONTS": ":".join(str(p/"fonts/tfm")+"//" for p in roots)+":",
                "T1FONTS": ":".join(str(p/"fonts/type1")+"//" for p in roots)+":",
                "ENCFONTS": ":".join(str(p/"fonts/enc")+"//" for p in roots)+":",
                "TEXFONTMAPS": str(runtime)+":"+":".join(str(p/"fonts/map")+"//" for p in roots)+":",
                "TEXFORMATS": str(runtime), "MKTEXFMT": "0",
            })
            (runtime/"language.dat").write_text("english hyphen.tex\n")
            maps = []
            for rel in ["fonts/map/dvips/lm/lm.map", "fonts/map/dvips/amsfonts/cm.map",
                        "fonts/map/dvips/amsfonts/cmextra.map",
                        "fonts/map/dvips/amsfonts/symbols.map",
                        "fonts/map/dvips/amsfonts/latxfont.map"]:
                found = next((p/rel for p in roots if (p/rel).is_file()), None)
                if found:
                    maps.append(found.read_text())
            (runtime/"pdftex.map").write_text("\n".join(maps))
            ini = roots[0]/"tex/latex/tex-ini-files/pdflatex.ini"
            execute(["pdftex", "-ini", "-etex", "-progname=pdflatex",
                     "-jobname=pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                     "-no-shell-escape", str(ini)], env,
                    verification/"tex-format.log", runtime)
            command = ["pdftex", "-fmt=pdflatex", "-progname=pdflatex"]
        for n in range(1, 4):
            execute(command + ["-interaction=nonstopmode", "-halt-on-error",
                               "-no-shell-escape", source], env,
                    verification/f"tex-pass-{n}.log", root)
            print(f"LaTeX pass {n}: success")
    print(root / "faltings_ipra.pdf")


if __name__ == "__main__":
    main()
