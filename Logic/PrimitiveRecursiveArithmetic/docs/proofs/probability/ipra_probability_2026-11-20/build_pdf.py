"""Build the report from its complete LaTeX sources; Python 3 standard library.

Normally only a complete TeX Live/MiKTeX pdflatex installation is needed.
Optional IPRA_PDF_FORMAT and IPRA_FONT_MAP_DIR support a separately prepared
local pdfLaTeX format and font map; compiler binaries are not bundled.
"""
import os
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PAPER = ROOT / "paper"
env = os.environ.copy()
binary = env.get("IPRA_PDFLATEX", "pdflatex")
if shutil.which(binary) is None:
    raise SystemExit("Install pdfLaTeX or set IPRA_PDFLATEX to its executable.")

# Some minimal Linux installations have the assets but no kpathsea file index.
# These explicit recursive paths leave an ordinary configured install usable.
asset_roots = [Path(p) for p in ("/usr/share/texlive/texmf-dist", "/usr/share/texmf")]
asset_roots = [p for p in asset_roots if (p / "tex").exists()]
if asset_roots:
    for name, suffix in (("TEXINPUTS", "tex"), ("TFMFONTS", "fonts/tfm"),
                         ("T1FONTS", "fonts/type1"), ("VFFONTS", "fonts/vf"),
                         ("ENCFONTS", "fonts/enc"), ("TEXFONTMAPS", "fonts/map")):
        existing = env.get(name, "")
        env[name] = ".:" + ":".join(str(p/suffix)+"//" for p in asset_roots) + ":" + existing
if env.get("IPRA_FONT_MAP_DIR"):
    env["TEXFONTMAPS"] = env["IPRA_FONT_MAP_DIR"]+"//:"+env.get("TEXFONTMAPS", "")
command = [binary]
if env.get("IPRA_PDF_FORMAT"):
    command += ["-fmt="+env["IPRA_PDF_FORMAT"]]
command += ["-interaction=nonstopmode", "-halt-on-error", "report.tex"]
receipts = []
for pass_number in range(1, 4):
    result = subprocess.run(command, cwd=PAPER, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    receipts.append(f"PASS {pass_number}\n"+result.stdout)
    if result.returncode:
        (ROOT/"validation"/"latex_build.log").write_text("\n".join(receipts))
        print(result.stdout[-7000:])
        raise SystemExit(result.returncode)
(ROOT/"validation"/"latex_build.log").write_text("\n".join(receipts))
log = (PAPER/"report.log").read_text(errors="replace")
problems = [line for line in log.splitlines()
            if any(x in line for x in ("Overfull ", "undefined references",
                                       "undefined citations", "Missing character:"))]
if problems:
    print("PDF built; preflight requires review:")
    print("\n".join(problems))
else:
    print("PDF built with no overfull boxes, missing characters, or unresolved references.")
print(PAPER/"report.pdf")
