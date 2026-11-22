#!/usr/bin/env python3
"""Compile the report with pdfLaTeX, including a minimal-TeX-install fallback."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def run(args, env, cwd, output):
    result = subprocess.run(args, cwd=cwd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    output.write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f"{args[0]} failed; see {output}")
    return result.stdout


def kpse(name, env):
    result = subprocess.run(["kpsewhich", name], env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return result.stdout.strip() if result.returncode == 0 else ""


def main():
    env = os.environ.copy()
    if not shutil.which("pdflatex") or not shutil.which("kpsewhich"):
        raise SystemExit("Install pdfLaTeX/TeX Live (AMS, Latin Modern, geometry, "
                         "microtype, booktabs, enumitem, xurl, hyperref, fancyhdr, listings).")
    evidence = ROOT / "evidence"
    evidence.mkdir(exist_ok=True)
    fallback = False
    if not kpse("article.cls", env):
        tree = Path("/usr/share/texlive/texmf-dist")
        if not (tree/"tex/latex/base/article.cls").exists():
            raise SystemExit("A usable LaTeX package tree was not found.")
        env["TEXMFDIST"] = str(tree)
        env["TEXMF"] = "{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
        fallback = True
    with tempfile.TemporaryDirectory(prefix="ipra-tex-") as private:
        private = Path(private)
        if not kpse("pdflatex.fmt", env):
            run(["pdflatex","-ini","-etex","-jobname=pdflatex","-progname=pdflatex",
                 "-interaction=nonstopmode","-halt-on-error","pdflatex.ini"],
                env,private,evidence/"pdf_format_build.log")
            env["TEXFORMATS"] = str(private)+os.pathsep+env.get("TEXFORMATS","")
            fallback = True
        if not kpse("pdftex.map", env):
            maps = list(Path("/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts").glob("*.map"))
            lm = Path("/usr/share/texmf/fonts/map/dvips/lm/lm.map")
            if lm.exists():
                maps.append(lm)
            if not maps:
                raise SystemExit("No font map is available; run updmap for your TeX installation.")
            lines, seen = [], set()
            for f in maps:
                for line in f.read_text().splitlines():
                    words=line.split()
                    if not words or line.startswith("%") or words[0] in seen:
                        continue
                    seen.add(words[0])
                    lines.append(line)
            (private/"pdftex.map").write_text("\n".join(lines)+"\n")
            env["TEXFONTMAPS"]=str(private)+os.pathsep+env.get("TEXFONTMAPS","")
            fallback = True
        for i in range(1,4):
            run(["pdflatex","-interaction=nonstopmode","-halt-on-error","report.tex"],
                env,ROOT,evidence/f"pdf_pass_{i}.log")
    final=(ROOT/"report.log").read_text()
    (evidence/"pdf_build.log").write_text(final)
    bad = [s for s in final.splitlines()
           if "undefined" in s.lower() or "Overfull" in s or "Missing character:" in s]
    if bad:
        raise RuntimeError("PDF needs layout/reference review:\n"+"\n".join(bad))
    info=""
    if shutil.which("pdfinfo"):
        info=subprocess.check_output(["pdfinfo",str(ROOT/"report.pdf")],text=True)
        (evidence/"pdfinfo.txt").write_text(info)
    status={"status":"compiled","engine":"pdfLaTeX","passes":3,
            "minimal_install_fallback":fallback,"undefined_references":False,
            "overfull_boxes":False,"missing_characters":False,
            "visual_review":"separate; compilation alone is not visual QA"}
    (evidence/"pdf_build.json").write_text(json.dumps(status,indent=2)+"\n")
    for suffix in ["aux","log","out","toc"]:
        (ROOT/f"report.{suffix}").unlink(missing_ok=True)
    print(json.dumps(status,indent=2))


if __name__=="__main__":
    main()
