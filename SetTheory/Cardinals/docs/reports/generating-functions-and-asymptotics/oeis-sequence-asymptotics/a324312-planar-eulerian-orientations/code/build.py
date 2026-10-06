#!/usr/bin/env python3
"""Build Report171 in a clean temporary tree and create a deterministic no-clobber ZIP."""
from __future__ import annotations

import argparse
import datetime
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "code"))
from companion import ValidationError, json_bytes, require, write_new

# 2026-10-03 00:00:00 UTC; independent of wall clock, locale and invoking directory.
SOURCE_DATE_EPOCH = 1790985600
ZIP_TIME = (2026, 10, 3, 0, 0, 0)
SOURCE_FILES = ["Report171.tex", "README.md", "requirements.txt", "build.py",
                "code/companion.py", "code/test_companion.py", "code/test_build.py",
                "fixtures/SHA256.json", "fixtures/oeis_prefixes.json",
                "fixtures/eulerian_coefficients.json", "fixtures/local_sector_coefficients.json",
                "fixtures/provenance.json"]


def make_zip_bytes_tree(directory, destination):
    """ZIP_STORED avoids dependence on the compression library version."""
    directory, destination = Path(directory), Path(destination)
    files = sorted(p for p in directory.rglob("*") if p.is_file())
    with zipfile.ZipFile(destination, "x", compression=zipfile.ZIP_STORED) as archive:
        for path in files:
            require(not path.is_symlink(), "archive input contains symlink")
            info = zipfile.ZipInfo(path.relative_to(directory).as_posix(), ZIP_TIME)
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_STORED
            info.flag_bits = 0
            archive.writestr(info, path.read_bytes())


def manifest(directory):
    return {p.relative_to(directory).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(directory.rglob("*")) if p.is_file() and p.name != "SHA256SUMS.json"}


def run(command, cwd, env, timeout=600):
    result = subprocess.run(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, timeout=timeout)
    if result.returncode:
        raise ValidationError("command failed: " + " ".join(map(str, command)) + "\n" + result.stdout[-16000:])
    return result.stdout


def prepare_tex(texwork, env):
    """Recover an installed TeX tree whose generated database/format is absent.

    Only local build files are created. No package installation or global repair.
    On a complete installation, the ordinary TeX lookup configuration is retained.
    """
    probe = subprocess.run(["kpsewhich", "pdflatex.fmt"], env=env, capture_output=True, text=True)
    if probe.returncode == 0 and probe.stdout.strip():
        return "system format"
    require(shutil.which("pdftex") is not None, "pdftex is required to initialize the missing format")
    distribution = Path(run(["kpsewhich", "-var-value=TEXMFDIST"], texwork, env).strip())
    require(distribution.is_dir(), "installed TeX distribution was not found")
    trees = [distribution]
    sibling = distribution.parent.parent / "texmf"
    if sibling.is_dir():
        trees.append(sibling)
    # Omit the usual !! prefixes, which prohibit filesystem fallback when ls-R is missing.
    env["TEXMF"] = "{" + ",".join(map(str, trees)) + "}"
    env["TEXFORMATS"] = str(texwork) + os.pathsep
    run(["pdftex", "-ini", "-etex", "-no-shell-escape", "-interaction=nonstopmode",
         "-halt-on-error", "-jobname=pdflatex", "pdflatex.ini"], texwork, env, timeout=180)
    require((texwork / "pdflatex.fmt").is_file(), "format initialization did not produce pdflatex.fmt")
    # This report uses Computer Modern/AMS and Latin Modern. The usual generated
    # pdftex.map may be absent for the same reason as the format; assemble its
    # relevant installed component maps in deterministic order.
    maps = []
    for name in ["cm.map", "cmextra.map", "latxfont.map", "symbols.map", "lm.map"]:
        path = Path(run(["kpsewhich", name], texwork, env).strip())
        require(path.is_file(), f"installed font map is missing: {name}")
        maps.append(path.read_bytes())
    write_new(texwork / "pdftex.map", b"\n".join(maps) + b"\n")
    return "temporary format and installed component font maps"


def compile_pdf(source, texwork, env):
    """Compile at least twice, at most six times, until aux/toc/out are stable."""
    write_new(texwork / "Report171.tex", Path(source).read_bytes())
    command = ["pdflatex", "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error",
               "-file-line-error", "-jobname=Report171",
               r"\pdfinfoomitdate=1\relax\pdftrailerid{}\pdfsuppressptexinfo=15\relax\input{Report171.tex}"]
    previous = None
    for iteration in range(1, 7):
        output = run(command, texwork, env, timeout=180)
        state = tuple((texwork / ("Report171." + suffix)).read_bytes()
                      if (texwork / ("Report171." + suffix)).exists() else b""
                      for suffix in ["aux", "toc", "out"])
        if iteration >= 2 and state == previous:
            break
        previous = state
    else:
        raise ValidationError("TeX auxiliary files did not settle in six passes")
    log = (texwork / "Report171.log").read_text(errors="replace")
    require("There were undefined references" not in log and "Rerun to get cross-references right" not in log,
            "TeX references remain unresolved")
    defects = re.findall(r"(?:Overfull[^\n]*|Missing character:[^\n]*)", log, flags=re.IGNORECASE)
    require(not defects, "TeX layout/glyph defect: " + "; ".join(defects))
    pdf = texwork / "Report171.pdf"
    require(pdf.is_file() and pdf.read_bytes().startswith(b"%PDF-"), "pdflatex did not produce a valid PDF")
    return iteration


def build(destination, pdf_output=None):
    destination = Path(destination).absolute()
    pdf_output = Path(pdf_output).absolute() if pdf_output else None
    if pdf_output:
        require(destination != pdf_output, "ZIP and PDF destinations must differ")
    for target in [destination] + ([pdf_output] if pdf_output else []):
        require(not target.exists() and not target.is_symlink(), f"refusing existing destination: {target}")
        require(target.parent.is_dir(), f"destination parent does not exist: {target.parent}")
    require(shutil.which("pdflatex") is not None, "pdflatex is required")
    require(datetime.datetime.fromtimestamp(SOURCE_DATE_EPOCH, datetime.timezone.utc).timetuple()[:6] == ZIP_TIME,
            "inconsistent deterministic timestamps")
    env = dict(os.environ, SOURCE_DATE_EPOCH=str(SOURCE_DATE_EPOCH), FORCE_SOURCE_DATE="1",
               TZ="UTC", LC_ALL="C.UTF-8", PYTHONDONTWRITEBYTECODE="1", PYTHONHASHSEED="0")
    with tempfile.TemporaryDirectory(prefix="report171-build-") as temporary:
        work = Path(temporary)
        # Some installations generate format/font caches lazily. Keep those writes
        # inside the build tree instead of requiring a writable user home directory.
        env.update(TEXMFVAR=str(work / "texmf-var"), TEXMFCONFIG=str(work / "texmf-config"),
                   TEXMFCACHE=str(work / "texmf-cache"))
        texwork = work / "tex"
        texwork.mkdir()
        tex_mode = prepare_tex(texwork, env)
        package = work / "package"
        package.mkdir()
        for name in SOURCE_FILES:
            source, target = ROOT / name, package / name
            require(source.is_file() and not source.is_symlink(), f"missing regular source: {name}")
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
            os.chmod(target, 0o644)
            os.utime(target, (SOURCE_DATE_EPOCH, SOURCE_DATE_EPOCH))
        (package / "outputs").mkdir()
        for optimized, name in [(False, "tests.json"), (True, "tests_optimized.json")]:
            run([sys.executable] + (["-O"] if optimized else []) +
                ["code/test_companion.py", "--output", "outputs/" + name], package, env)
        run([sys.executable, "code/test_build.py", "--output", "outputs/build_tests.json"], package, env)
        run([sys.executable, "-O", "code/test_build.py", "--output", "outputs/build_tests_optimized.json"], package, env)
        run([sys.executable, "code/companion.py", "exact", "--n", "1000", "--lagrange-m", "81",
             "--output", "outputs/exact.json"], package, env)
        run([sys.executable, "code/companion.py", "symbolic", "--output", "outputs/symbolic.json"], package, env)
        run([sys.executable, "code/companion.py", "diagnostics", "--n", "1000", "--digits", "110",
             "--prefix", "60", "--output", "outputs/diagnostics_110d.json"], package, env)
        for sequence in ["A277493", "A324312", "A324314"]:
            run([sys.executable, "code/companion.py", "inverse", "--sequence", sequence,
                 "--log-y", "1000", "--digits", "110", "--output",
                 "outputs/inverse_" + sequence + "_logy1000.json"], package, env)
        passes = compile_pdf(package / "Report171.tex", texwork, env)
        info = {"source_date_epoch": SOURCE_DATE_EPOCH, "zip_compression": "ZIP_STORED",
                "python": sys.version.split()[0],
                "sympy": importlib.metadata.version("sympy"), "mpmath": importlib.metadata.version("mpmath"),
                "pdflatex": run(["pdflatex", "--version"], package, env).splitlines()[0],
                "tex_initialization": tex_mode,
                "latex_passes": passes,
                "reproducibility_scope": "Byte-identical with identical sources and toolchain; PDF rendering can differ across TeX installations.",
                "manifest_note": "SHA256SUMS.json lists every packaged file except itself."}
        write_new(package / "BUILD-INFO.json", json_bytes(info))
        shutil.copyfile(texwork / "Report171.pdf", package / "Report171.pdf")
        write_new(package / "SHA256SUMS.json", json_bytes(manifest(package)))
        temporary_zip = work / "Report171.zip"
        make_zip_bytes_tree(package, temporary_zip)
        # Final creation remains exclusive even if another process wrote a destination meanwhile.
        # If both requested, PDF is installed first; a later ZIP creation failure leaves it intact.
        if pdf_output:
            write_new(pdf_output, (package / "Report171.pdf").read_bytes())
        write_new(destination, temporary_zip.read_bytes())
        return {"archive": str(destination), "sha256": hashlib.sha256(destination.read_bytes()).hexdigest(),
                "bytes": destination.stat().st_size, "pdf": str(pdf_output) if pdf_output else None}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="new ZIP path (never overwritten)")
    parser.add_argument("--pdf-output", type=Path, help="also copy the compiled PDF to this new path")
    args = parser.parse_args()
    try:
        print(json.dumps(build(args.output, args.pdf_output), indent=2, sort_keys=True))
    except (ValueError, OSError, subprocess.TimeoutExpired) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
