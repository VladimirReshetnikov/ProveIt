"""Compile the report, including on minimal TeX Live installations.

The temporary fallback supplies generated format or font-map files when
the packages are present but those generated files are absent. It does
not change the system TeX installation or download packages.
"""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def locate(name):
    result = subprocess.run(["kpsewhich", name], text=True, capture_output=True)
    return result.stdout.strip() if result.returncode == 0 else ""


def main():
    for tool in ("pdflatex", "kpsewhich"):
        if shutil.which(tool) is None:
            raise SystemExit(tool + " is required to compile the report")
    env = os.environ.copy()
    with tempfile.TemporaryDirectory(prefix="ipra-tex-") as scratch:
        temporary = Path(scratch)
        if not locate("pdflatex.fmt"):
            if shutil.which("pdftex") is None or not locate("pdflatex.ini"):
                raise SystemExit("Install the LaTeX format for pdfTeX first")
            subprocess.run(
                ["pdftex", "-ini", "-etex", "-jobname=pdflatex",
                 "-progname=pdflatex", "pdflatex.ini"],
                cwd=temporary, env=env, check=True,
            )
            env["TEXFORMATS"] = scratch + os.pathsep + env.get("TEXFORMATS", "")
        if not locate("pdftex.map"):
            maps = []
            for name in ("lm.map", "cm.map", "cmextra.map", "symbols.map",
                         "euler.map", "latxfont.map"):
                path = locate(name)
                if path:
                    maps.append(Path(path).read_text())
            if not maps:
                raise SystemExit("Install scalable Latin Modern and AMS fonts first")
            (temporary / "pdftex.map").write_text("\n".join(maps))
            env["TEXFONTMAPS"] = scratch + os.pathsep + env.get("TEXFONTMAPS", "")
        for _ in range(3):
            subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                 "-file-line-error", "ipra_all_starts.tex"],
                cwd=ROOT, env=env, check=True,
            )
    print(ROOT / "ipra_all_starts.pdf")


if __name__ == "__main__":
    main()
