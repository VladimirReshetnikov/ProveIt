"""Compile the report three times using installed TeX, without global changes.

Normal pdfLaTeX is tried first.  If its format or filename cache is missing,
the fallback searches installed TeX trees directly and creates a private
format in a TemporaryDirectory.  Nothing is downloaded, and no format from
another workspace is used.  A complete TeX installation is still required.
"""
# Adapted from the pinned incoming ipra_constantfree archive under MIT-0.
import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent


def installed_roots(pdftex, environment):
    candidates = []
    kpsewhich = shutil.which("kpsewhich")
    if kpsewhich:
        for variable in ("TEXMFDIST", "TEXMFLOCAL", "TEXMFDEBIAN"):
            result = subprocess.run([kpsewhich, "-var-value=" + variable],
                                    env=environment, capture_output=True, text=True)
            value = result.stdout.strip()
            if result.returncode == 0 and value:
                candidates.append(Path(value))
    candidates.extend(Path(p) for p in ("/usr/share/texlive/texmf-dist",
                                       "/usr/share/texmf", "/usr/local/share/texmf"))
    for parent in Path(pdftex).resolve().parents:
        candidates.extend((parent / "texmf-dist", parent / "share/texmf",
                           parent / "share/texlive/texmf-dist"))
    roots = []
    for candidate in candidates:
        if candidate.is_dir() and candidate.resolve() not in roots:
            roots.append(candidate.resolve())
    return roots


def direct_search_environment(environment, roots, source_directory, format_directory):
    result = environment.copy()
    # Explicit paths have no !! prefix, so a missing ls-R database is harmless.
    inputs = [str(source_directory)]
    for root in roots:
        for relative in ("tex/latex/base", "tex/latex/tex-ini-files",
                         "tex/generic/tex-ini-files", "tex/latex//",
                         "tex/generic//", "tex//"):
            inputs.append(str(root) + "/" + relative)
    result["TEXINPUTS"] = os.pathsep.join(inputs) + os.pathsep
    for variable, relative in (("TFMFONTS", "fonts/tfm//"),
                               ("T1FONTS", "fonts/type1//"),
                               ("VFFONTS", "fonts/vf//"),
                               ("ENCFONTS", "fonts/enc//"),
                               ("TEXFONTMAPS", "fonts/map//"),
                               ("TEXPSHEADERS", "fonts//")):
        result[variable] = os.pathsep.join(str(root) + "/" + relative
                                            for root in roots) + os.pathsep
    # Deliberately no default expansion: only our freshly generated format.
    result["TEXFORMATS"] = str(format_directory)
    return result


def build(source, destination, log_path):
    pdflatex = shutil.which("pdflatex")
    pdftex = shutil.which("pdftex")
    if not pdflatex:
        raise RuntimeError("pdfLaTeX is unavailable; install a conventional TeX Live distribution.")
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="ipra-pdf-") as temporary:
        temporary = Path(temporary)
        work = temporary / "work"
        formats = temporary / "formats"
        work.mkdir()
        formats.mkdir()
        environment = os.environ.copy()
        environment.pop("TEXFORMATS", None)
        environment.update({"TEXMFVAR": str(temporary / "texmf-var"),
                            "TEXMFCONFIG": str(temporary / "texmf-config"),
                            "TEXMFOUTPUT": str(work), "MKTEXFMT": "0",
                            "MKTEXPK": "0", "MKTEXTFM": "0"})
        environment["TEXINPUTS"] = str(source.parent) + os.pathsep + environment.get("TEXINPUTS", "")
        options = ["-interaction=nonstopmode", "-halt-on-error", "-file-line-error",
                   "-no-shell-escape", "-no-mktex=fmt", "-output-directory=" + str(work)]
        with log_path.open("w", encoding="utf-8") as log:
            def run(label, command, env):
                log.write("\n=== " + label + " ===\n" + repr(command) + "\n")
                log.flush()
                result = subprocess.run(command, cwd=work, env=env, stdin=subprocess.DEVNULL,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                        text=True, errors="replace", timeout=120)
                log.write(result.stdout)
                log.flush()
                return result

            command = [pdflatex, *options, str(source)]
            first = run("installed pdfLaTeX, pass 1", command, environment)
            method = "installed pdfLaTeX"
            if first.returncode:
                if not pdftex:
                    raise RuntimeError("pdfLaTeX failed and pdftex is unavailable for private format generation; see " + str(log_path))
                roots = installed_roots(pdftex, environment)
                ini = next((root / "tex/latex/tex-ini-files/pdflatex.ini" for root in roots
                            if (root / "tex/latex/tex-ini-files/pdflatex.ini").is_file()), None)
                if ini is None:
                    raise RuntimeError("Installed pdflatex.ini was not found. A complete TeX Live installation is required; see " + str(log_path))
                environment = direct_search_environment(environment, roots, source.parent, formats)
                # This runtime can contain installed Type 1 fonts without a
                # generated pdftex.map. Build only a private, task-local map.
                font_maps = []
                for relative in ("fonts/map/dvips/lm/lm.map",
                                 "fonts/map/dvips/amsfonts/cm.map",
                                 "fonts/map/dvips/amsfonts/cmextra.map",
                                 "fonts/map/dvips/amsfonts/symbols.map",
                                 "fonts/map/dvips/amsfonts/latxfont.map"):
                    found = next((root / relative for root in roots
                                  if (root / relative).is_file()), None)
                    if found is not None:
                        font_maps.append(found.read_text())
                if font_maps:
                    (work / "pdftex.map").write_text("\n".join(font_maps))
                    environment["TEXFONTMAPS"] = str(work) + os.pathsep + environment["TEXFONTMAPS"]
                initialize = [pdftex, "-ini", "-etex", "-progname=pdflatex", "-jobname=pdflatex",
                              "-interaction=nonstopmode", "-halt-on-error", "-no-shell-escape",
                              "-output-directory=" + str(formats), str(ini)]
                initialized = run("create private format from installed pdflatex.ini", initialize, environment)
                if initialized.returncode or not (formats / "pdflatex.fmt").is_file():
                    raise RuntimeError("Private format generation failed. Install the missing TeX dependencies reported in " + str(log_path))
                command = [pdftex, "-fmt=pdflatex", "-progname=pdflatex", *options, str(source)]
                method = "private format from installed TeX sources"
                first = run("private-format pdfLaTeX, pass 1", command, environment)
                if first.returncode:
                    raise RuntimeError("PDF compilation failed after private format generation; see " + str(log_path))
            for number in (2, 3):
                result = run("pdfLaTeX, pass " + str(number), command, environment)
                if result.returncode:
                    raise RuntimeError("PDF compilation failed on pass " + str(number) + "; see " + str(log_path))
            output = work / (source.stem + ".pdf")
            if not output.is_file():
                raise RuntimeError("TeX reported success but produced no PDF; see " + str(log_path))
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(output, destination)
            final_log = (work / (source.stem + ".log")).read_text(errors="replace")
            shutil.copyfile(work / (source.stem + ".log"), destination.with_suffix(".log"))
            page_match = re.search(r"Output written on .*?\((\d+) pages?[,)]", final_log, re.S)
            pages = page_match.group(1) if page_match else "unknown"
            warnings = [line for line in final_log.splitlines()
                        if "Overfull" in line or "undefined" in line.lower() or "Warning:" in line]
            print("PDF built in three passes using " + method + ".")
            print("Output: " + str(destination) + " (" + pages + " pages)")
            print("Build log: " + str(log_path))
            print("Final-pass warnings: " + str(len(warnings)))
            for warning in warnings:
                print(warning)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tex", type=Path, default=ROOT / "ipra_single_binder.tex")
    parser.add_argument("--output", type=Path, default=ROOT / "ipra_single_binder.pdf")
    parser.add_argument("--log", type=Path, default=ROOT / "evidence/pdf_build.log")
    arguments = parser.parse_args()
    try:
        build(arguments.tex.resolve(), arguments.output.resolve(), arguments.log.resolve())
    except (RuntimeError, subprocess.TimeoutExpired, OSError) as error:
        print("PDF build failed: " + str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
