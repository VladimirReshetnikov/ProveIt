#!/usr/bin/env python3
"""Build Report174 in a fresh isolated directory, with no overwrite option."""
import argparse
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True

from package_tools import (EPOCH, GENERATED_FILES, PAYLOAD_FILES, REPORT, SOURCE_FILES,
                           PackageError, create_zip, deterministic_environment, digest,
                           json_bytes, make_manifest, require, safe_regular_file,
                           verify_directory)


def command(args, cwd, env, log, timeout):
    try:
        result = subprocess.run(args, cwd=cwd, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=timeout, check=False)
    except subprocess.TimeoutExpired as exc:
        with log.open("ab") as stream:
            stream.write(exc.stdout or b"")
        raise PackageError(f"command exceeded {timeout}s: {args[0]}") from exc
    with log.open("ab") as stream:
        stream.write(("$ "+" ".join(map(str, args))+"\n").encode())
        stream.write(result.stdout)
    require(result.returncode == 0, f"command failed ({result.returncode}); see {log}")
    return result.stdout



def prepare_tex(work, env, log, timeout):
    """Use installed TeX files; recover a missing format entirely inside work."""
    require(shutil.which("kpsewhich") is not None, "kpsewhich is required")
    probe = subprocess.run(["kpsewhich", "pdflatex.fmt"], env=env,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    if probe.returncode == 0 and probe.stdout.strip():
        return
    require(shutil.which("pdftex") is not None, "pdftex is needed for local format initialization")
    dist = Path(command(["kpsewhich", "-var-value=TEXMFDIST"], work, env, log, timeout).decode().strip())
    require(dist.is_dir(), "installed TeX distribution was not found")
    trees = [dist]
    sibling = dist.parent.parent/"texmf"
    if sibling.is_dir():
        trees.append(sibling)
    env["TEXMF"] = "{"+",".join(map(str, trees))+"}"
    env["TEXFORMATS"] = str(work)+os.pathsep
    command(["pdftex", "-ini", "-etex", "-no-shell-escape", "-interaction=nonstopmode",
             "-halt-on-error", "-jobname=pdflatex", "pdflatex.ini"], work, env, log, timeout)
    require((work/"pdflatex.fmt").is_file(), "local pdflatex format was not created")
    maps = []
    for name in ("cm.map", "cmextra.map", "latxfont.map", "symbols.map", "lm.map"):
        path = Path(command(["kpsewhich", name], work, env, log, timeout).decode().strip())
        require(path.is_file(), "installed font map was not found: "+name)
        maps.append(path.read_bytes())
    (work/"pdftex.map").write_bytes(b"\n".join(maps)+b"\n")


def python_command(script, flags=(), optimized=False):
    # -I excludes user site and PYTHONPATH; insert only the copied script folder.
    runner = ("import runpy,sys; sys.path.insert(0,sys.argv[1]); "
              "sys.argv=sys.argv[2:]; runpy.run_path(sys.argv[0],run_name='__main__')")
    return [sys.executable, "-I", "-B", *(["-O"] if optimized else []), "-c", runner,
            str(script.parent), str(script), *flags]

def build(source, output, extended=False, timeout=300):
    source, output = Path(source).resolve(), Path(output).absolute()
    require(output.resolve() != source, "output cannot equal source")
    require(not output.exists() and not output.is_symlink(), "output directory already exists; choose a fresh name")
    for name in SOURCE_FILES:
        safe_regular_file(source, name)
    latex = shutil.which("pdflatex")
    require(latex is not None, "pdflatex is required; install a TeX distribution")
    require(output.parent.is_dir(), "output parent directory does not exist")
    # mkdir is exclusive and is never retried by overwriting an existing directory.
    output.mkdir()
    log = output / "build.log"
    env = deterministic_environment()
    try:
        with tempfile.TemporaryDirectory(prefix=".isolated-", dir=output) as work_name:
            work = Path(work_name)
            env.update(TEXMFVAR=str(work/"tex-var"), TEXMFCONFIG=str(work/"tex-config"),
                       TEXMFCACHE=str(work/"tex-cache"), openout_any="p")
            stage = work / REPORT
            stage.mkdir()
            for name in SOURCE_FILES:
                destination = stage/name
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(safe_regular_file(source, name).read_bytes())
            check_flags = ["--extended"] if extended else []
            python = sys.executable
            normal = command(python_command(stage/"companion/run_checks.py", check_flags), stage, env, log, timeout)
            optimized = command(python_command(stage/"companion/run_checks.py", check_flags, True), stage, env, log, timeout)
            require(json.loads(normal) == json.loads(optimized), "normal and -O verification results differ")
            (stage/"verification.json").write_bytes(normal)
            command(python_command(stage/"test_package_tools.py"), stage, env, log, timeout)
            command(python_command(stage/"test_package_tools.py", optimized=True), stage, env, log, timeout)
            tex_work = work/"latex"
            tex_work.mkdir()
            prepare_tex(tex_work, env, log, timeout)
            (tex_work/"Report174.tex").write_bytes((stage/"Report174.tex").read_bytes())
            tex_command = [latex, "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error",
                           "-file-line-error", "-jobname=Report174",
                           r"\pdfinfoomitdate=1\pdftrailerid{}\pdfsuppressptexinfo=15\input{Report174.tex}"]
            previous = None
            for passes in range(1, 7):
                command(tex_command, tex_work, env, log, timeout)
                state = tuple((tex_work/(REPORT+"."+suffix)).read_bytes()
                              if (tex_work/(REPORT+"."+suffix)).exists() else b""
                              for suffix in ("aux", "toc", "out"))
                if passes >= 2 and state == previous:
                    break
                previous = state
            else:
                raise PackageError("LaTeX auxiliary files did not stabilize in six passes")
            tex_log = (tex_work/"Report174.log").read_text(encoding="utf-8", errors="replace")
            failures = ("There were undefined references", "There were undefined citations",
                        "Rerun to get cross-references right", "Label(s) may have changed")
            require(not any(x in tex_log for x in failures), "unresolved references after LaTeX stabilization")
            defects = re.findall(r"(?:Overfull[^\n]*|Missing character:[^\n]*)", tex_log, re.I)
            require(not defects, "LaTeX layout or glyph defect: "+"; ".join(defects))
            pdf = (tex_work/"Report174.pdf").read_bytes()
            require(pdf.startswith(b"%PDF-"), "invalid PDF output")
            (stage/"Report174.pdf").write_bytes(pdf)
            version = subprocess.run([latex, "--version"], env=env, text=True,
                                     stdout=subprocess.PIPE, check=True, timeout=timeout).stdout.splitlines()[0]
            (stage/"build_info.json").write_bytes(json_bytes({
                "schema": "Report174.build.v1", "report": REPORT,
                "verification_mode": "extended" if extended else "default",
                "python_version": platform.python_version(), "pdflatex_version": version,
                "source_date_epoch": EPOCH, "latex_passes": passes,
                "shell_escape": False, "normal_and_optimized_python_checked": True,
                "archive": {"compression": "deflate-9", "fixed_timestamp": "2026-10-03T00:00:00Z"},
                "reproducibility_scope": "byte-identical with the same Python, libm, TeX, fonts and zlib toolchain"}))
            (stage/"manifest.json").write_bytes(json_bytes(make_manifest(stage)))
            verify_directory(stage)
            create_zip(stage, output/(REPORT+".zip"))
            stage.rename(output/REPORT)
        verify_directory(output/REPORT)
        (output/"SHA256SUMS.txt").write_text(
            digest(output/(REPORT+".zip"))+"  "+REPORT+".zip\n"+
            digest(output/REPORT/"Report174.pdf")+"  "+REPORT+"/Report174.pdf\n"+
            digest(output/REPORT/"manifest.json")+"  "+REPORT+"/manifest.json\n", encoding="ascii")
        return {"package": str(output/REPORT), "pdf": str(output/REPORT/"Report174.pdf"),
                "zip": str(output/(REPORT+".zip")), "zip_sha256": digest(output/(REPORT+".zip"))}
    except Exception:
        (output/"BUILD_FAILED.txt").write_text("Build did not complete. Inspect build.log; retry only with a fresh output directory.\n", encoding="utf-8")
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--output", required=True, type=Path, help="new, nonexistent output directory")
    parser.add_argument("--extended", action="store_true", help="package extended bounded verification results")
    parser.add_argument("--timeout", type=int, default=300, help="per-command wall-time limit, seconds (1..3600)")
    args = parser.parse_args()
    try:
        require(1 <= args.timeout <= 3600, "timeout must be in 1..3600")
        result = build(args.source, args.output, args.extended, args.timeout)
        print(json.dumps(result, indent=2, sort_keys=True))
    except (PackageError, OSError, subprocess.SubprocessError, ValueError) as exc:
        print(f"build failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
