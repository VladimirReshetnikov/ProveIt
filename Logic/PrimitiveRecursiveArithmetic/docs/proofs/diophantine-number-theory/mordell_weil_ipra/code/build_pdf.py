#!/usr/bin/env python3
"""Build the paper; --local-tex also supports unindexed Debian TeX sources."""
from pathlib import Path
import argparse
import json
import os
import subprocess
import tempfile

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--local-tex", action="store_true")
    parser.add_argument("--runtime", type=Path)
    args = parser.parse_args()
    package = Path(__file__).resolve().parents[1]
    paper = package / "paper"
    metadata = package / "metadata"
    env = dict(os.environ)
    engine = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
              "-no-shell-escape"]
    runtime = args.runtime
    if args.local_tex:
        runtime = runtime or Path(tempfile.mkdtemp(prefix="mw_tex_"))
        runtime.mkdir(parents=True, exist_ok=True)
        roots = [Path("/usr/share/texlive/texmf-dist"), Path("/usr/share/texmf")]
        for variable, subdir in [
            ("TEXINPUTS", "tex"), ("TFMFONTS", "fonts/tfm"),
            ("T1FONTS", "fonts/type1"), ("ENCFONTS", "fonts/enc"),
            ("TEXFONTMAPS", "fonts/map")]:
            env[variable] = str(runtime) + ":.:" + ":".join(
                str(p / subdir) + "//" for p in roots) + ":"
        env["TEXFORMATS"] = str(runtime)
        env["MKTEXFMT"] = "0"
        (runtime / "language.dat").write_text("english hyphen.tex\n")
        maps = []
        for relative in [
            "fonts/map/dvips/lm/lm.map", "fonts/map/dvips/amsfonts/cm.map",
            "fonts/map/dvips/amsfonts/cmextra.map",
            "fonts/map/dvips/amsfonts/symbols.map",
            "fonts/map/dvips/amsfonts/latxfont.map"]:
            source = next((r / relative for r in roots if (r / relative).is_file()), None)
            if source:
                maps.append(source.read_text())
        (runtime / "pdftex.map").write_text("\n".join(maps))
        if not (runtime / "pdflatex.fmt").is_file():
            command = ["pdftex", "-ini", "-etex", "-progname=pdflatex",
                       "-jobname=pdflatex", "-interaction=nonstopmode",
                       "-halt-on-error", "-no-shell-escape",
                       str(roots[0] / "tex/latex/tex-ini-files/pdflatex.ini")]
            result = subprocess.run(command, cwd=runtime, env=env,
                                    capture_output=True, text=True)
            (runtime / "format-build.txt").write_text(result.stdout + result.stderr)
            if result.returncode:
                print((result.stdout + result.stderr)[-7000:])
                raise SystemExit(result.returncode)
        engine = ["pdftex", "-fmt=pdflatex", "-progname=pdflatex",
                  "-interaction=nonstopmode", "-halt-on-error", "-no-shell-escape"]
    logs = []
    for iteration in range(1, 4):
        result = subprocess.run(engine + ["mordell_weil_ipra.tex"], cwd=paper,
                                env=env, capture_output=True, text=True)
        text = result.stdout + result.stderr
        logs.append(f"PASS {iteration}\n{text}")
        if result.returncode:
            (metadata / "pdf_build.txt").write_text("\n".join(logs))
            print(text[-9000:])
            raise SystemExit(result.returncode)
    (metadata / "pdf_build.txt").write_text("\n".join(logs))
    pdf = paper / "mordell_weil_ipra.pdf"
    print(json.dumps({"success": True, "pdf": str(pdf),
                      "size_bytes": pdf.stat().st_size,
                      "passes": 3, "local_tex": args.local_tex}))

if __name__ == "__main__":
    main()
