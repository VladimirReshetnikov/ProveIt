#!/usr/bin/env python3
"""Deterministic Report202 replay, PDF compilation, manifest checks, and ZIP.

A normal build validates the extracted package before doing any work, regenerates
all exact data and the PDF, and requires every public member to be byte-identical.
Use --initialize only to create a release from maintained source files.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
SOURCE_FILES = ("README.md", "Report202.tex", "build.py", "test_guards.py", "requirements.txt",
                "repro/README.md", "repro/check.py", "repro/diagnostics.py", "repro/test_guards.py",
                "repro/requirements.txt", "repro/data/fixtures.json")
DATA_FILES = ("repro/generated/exact_checks.json", "repro/generated/exact_data.json",
              "repro/generated/numerical_diagnostics.json", "repro/generated/manifest.json")
SOURCE_MANIFEST = "manifests/source_manifest.json"
PACKAGE_MANIFEST = "manifests/package_manifest.json"
PUBLIC_FILES = tuple(sorted(SOURCE_FILES + DATA_FILES + ("Report202.pdf", SOURCE_MANIFEST, PACKAGE_MANIFEST)))
MAX_FILE_BYTES = 16*1024*1024
SOURCE_DATE_EPOCH = "1791072000"  # 2026-10-04 00:00:00 UTC
ZIP_DATE = (1980, 1, 1, 0, 0, 0)


class BuildError(ValueError):
    """A malformed package, failed check, or failed reproducible build."""


def require(condition, message):
    if not condition:
        raise BuildError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def canonical_bytes(value):
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True, allow_nan=False)+"\n").encode("ascii")


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def strict_json(path):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"), object_pairs_hook=no_duplicate_keys,
            parse_constant=lambda x: (_ for _ in ()).throw(BuildError(f"Nonfinite JSON value: {x}")))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise BuildError(f"Invalid UTF-8 JSON: {Path(path).name}") from exc


def safe_relative(name):
    require(type(name) is str and bool(name), "Manifest path must be a nonempty string")
    require("\\" not in name and "\x00" not in name, "Manifest path contains a forbidden character")
    p = PurePosixPath(name)
    require(not p.is_absolute() and p.as_posix() == name and
            all(part not in ("", ".", "..") for part in name.split("/")),
            "Manifest path must be a canonical relative POSIX path")
    require(re.fullmatch(r"[A-Za-z0-9_./-]+", name) is not None, "Unsupported manifest path character")
    return p


def checked_file(root, name):
    p = safe_relative(name)
    target = Path(root).joinpath(*p.parts)
    current = Path(root)
    require(not current.is_symlink(), "Package root must not be a symlink")
    for part in p.parts:
        current = current/part
        require(not current.is_symlink(), f"Symlink is forbidden in package: {name}")
    require(target.is_file(), f"Missing regular package file: {name}")
    require(target.stat().st_size <= MAX_FILE_BYTES, f"Package file exceeds size limit: {name}")
    require(target.resolve().is_relative_to(Path(root).resolve()), "Package path escapes root")
    return target


def record(root, name):
    path = checked_file(root, name)
    require(path.stat().st_size <= MAX_FILE_BYTES, f"Package file exceeds size limit: {name}")
    raw = path.read_bytes()
    return {"path": name, "bytes": len(raw), "sha256": sha256(raw)}


def validate_records(root, records, expected):
    require(type(records) is list, "Manifest files must be an array")
    require(len(records) == len(expected), "Manifest file count does not match the public allowlist")
    names = []
    for item in records:
        require(type(item) is dict and set(item) == {"path", "bytes", "sha256"}, "Malformed manifest file record")
        safe_relative(item["path"])
        require(type(item["bytes"]) is int and item["bytes"] >= 0, "Manifest byte count must be a nonnegative integer")
        require(type(item["sha256"]) is str and re.fullmatch(r"[0-9a-f]{64}", item["sha256"]) is not None,
                "Manifest SHA-256 must be 64 lowercase hexadecimal characters")
        names.append(item["path"])
    require(names == sorted(expected), "Manifest paths are duplicate, missing, extra, or out of order")
    for item in records:
        actual = record(root, item["path"])
        require(item == actual, f"Hash or byte-count mismatch: {item['path']}")


def engine_banner():
    try:
        result = subprocess.run(["pdflatex", "--version"], check=True, capture_output=True, text=True,
                                timeout=30, env={**os.environ, "LC_ALL": "C"})
    except (OSError, subprocess.SubprocessError) as exc:
        raise BuildError("pdflatex must be installed for PDF replay") from exc
    lines = result.stdout.splitlines()
    require(bool(lines), "pdflatex returned no version banner")
    return lines[0]


def source_manifest(root, banner):
    return {"schema": "report202-source-manifest-v1", "source_date_epoch": SOURCE_DATE_EPOCH,
            "pdf_engine_banner": banner, "files": [record(root, x) for x in sorted(SOURCE_FILES)]}


def package_manifest(root):
    return {"schema": "report202-package-manifest-v1",
            "files": [record(root, x) for x in PUBLIC_FILES if x != PACKAGE_MANIFEST]}


def validate_package(root, check_toolchain=False):
    root = Path(root)
    require(root.is_dir() and not root.is_symlink(), "Package root must be a regular directory")
    actual = []
    actual_dirs = []
    expected_dirs = sorted({p.as_posix() for name in PUBLIC_FILES for p in PurePosixPath(name).parents if p.as_posix() != "."})
    for path in root.rglob("*"):
        require(not path.is_symlink(), "Package contains a forbidden symlink")
        if path.is_file(): actual.append(path.relative_to(root).as_posix())
        else:
            require(path.is_dir(), "Package contains a special filesystem object")
            actual_dirs.append(path.relative_to(root).as_posix())
    require(sorted(actual_dirs) == expected_dirs, "Package contains undeclared directories")
    require(sorted(actual) == list(PUBLIC_FILES), "Package contains missing or undeclared files")
    source_path = checked_file(root, SOURCE_MANIFEST)
    source = strict_json(source_path)
    require(type(source) is dict and set(source) == {"schema", "source_date_epoch", "pdf_engine_banner", "files"},
            "Malformed source manifest")
    require(source["schema"] == "report202-source-manifest-v1", "Unsupported source manifest schema")
    require(source["source_date_epoch"] == SOURCE_DATE_EPOCH, "Unexpected reproducible build epoch")
    require(type(source["pdf_engine_banner"]) is str and source["pdf_engine_banner"].startswith("pdfTeX ") and
            len(source["pdf_engine_banner"]) <= 200 and "\n" not in source["pdf_engine_banner"],
            "Malformed PDF engine banner")
    validate_records(root, source["files"], SOURCE_FILES)
    require(source_path.read_bytes() == canonical_bytes(source), "Source manifest JSON is noncanonical")
    package_path = checked_file(root, PACKAGE_MANIFEST)
    package = strict_json(package_path)
    require(type(package) is dict and set(package) == {"schema", "files"}, "Malformed package manifest")
    require(package["schema"] == "report202-package-manifest-v1", "Unsupported package manifest schema")
    validate_records(root, package["files"], tuple(x for x in PUBLIC_FILES if x != PACKAGE_MANIFEST))
    require(package_path.read_bytes() == canonical_bytes(package), "Package manifest JSON is noncanonical")
    if check_toolchain:
        require(source["pdf_engine_banner"] == engine_banner(),
                "PDF engine differs from the recorded release; use the same TeX toolchain for byte identity")
    return {"status": "PASS", "public_members": len(PUBLIC_FILES), "source_members": len(SOURCE_FILES)}


def run_checks(root):
    env = {**os.environ, "PYTHONHASHSEED": "0", "PYTHONDONTWRITEBYTECODE": "1"}
    prefix = [sys.executable] + (["-O"] if sys.flags.optimize else [])
    commands = {
        "reproduction": prefix + [str(checked_file(root, "repro/check.py")), "--diagnostics",
                                  "--out", str(Path(root)/"repro/generated")],
        "reproduction_guards": prefix + [str(checked_file(root, "repro/test_guards.py")), "--diagnostics"],
        "package_guards": prefix + [str(checked_file(root, "test_guards.py"))],
    }
    receipts = {}
    for label, command in commands.items():
        try:
            result = subprocess.run(command, check=True, capture_output=True, text=True,
                                    timeout=600, env=env)
            receipts[label] = json.loads(result.stdout)
        except (OSError, subprocess.SubprocessError, json.JSONDecodeError) as exc:
            raise BuildError(label + " replay failed") from exc
    return receipts


def clean_environment(work):
    work = Path(work)
    for name in ("home", "tmp", "texvar", "texconfig", "texcache", "texhome", "fonts"):
        (work/name).mkdir()
    return {"PATH": os.environ.get("PATH", os.defpath), "HOME": str(work/"home"),
        "TMPDIR": str(work/"tmp"), "SOURCE_DATE_EPOCH": SOURCE_DATE_EPOCH,
        "FORCE_SOURCE_DATE": "1", "TZ": "UTC", "LC_ALL": "C.UTF-8",
        "PYTHONHASHSEED": "0", "PYTHONDONTWRITEBYTECODE": "1",
        "TEXMFVAR": str(work/"texvar"), "TEXMFCONFIG": str(work/"texconfig"),
        "TEXMFCACHE": str(work/"texcache"), "TEXMFHOME": str(work/"texhome"),
        "VARTEXFONTS": str(work/"fonts"), "openin_any": "p", "openout_any": "p", "shell_escape": "f"}


def tex_command(command, work, env, timeout=180):
    try:
        result = subprocess.run(command, cwd=work, env=env, capture_output=True,
                                text=True, timeout=timeout, check=False)
    except (OSError, subprocess.SubprocessError) as exc:
        raise BuildError("TeX toolchain command failed to run") from exc
    require(result.returncode == 0, "TeX setup failed: "+" ".join(command)+"\n"+(result.stdout+result.stderr)[-4000:])
    return result.stdout.strip()


def prepare_tex(work, env):
    require(shutil.which("pdflatex", path=env["PATH"]) is not None and
            shutil.which("kpsewhich", path=env["PATH"]) is not None,
            "Installed pdflatex and kpsewhich are required")
    probe = subprocess.run(["kpsewhich", "pdflatex.fmt"], cwd=work, env=env,
                           capture_output=True, text=True, timeout=30, check=False)
    if probe.returncode == 0 and probe.stdout.strip():
        return
    require(shutil.which("pdftex", path=env["PATH"]) is not None,
            "Installed pdftex is required to initialize a private format")
    dist = Path(tex_command(["kpsewhich", "-var-value=TEXMFDIST"], work, env))
    require(dist.is_dir(), "Installed TeX tree is missing")
    trees = [dist]
    sibling = dist.parent.parent/"texmf"
    if sibling.is_dir(): trees.append(sibling)
    env["TEXMF"] = "{"+",".join(map(str, trees))+"}"
    env["TEXFORMATS"] = str(work)+os.pathsep
    tex_command(["pdftex", "-ini", "-etex", "-no-shell-escape", "-interaction=nonstopmode",
                 "-halt-on-error", "-jobname=pdflatex", "pdflatex.ini"], work, env)
    require((work/"pdflatex.fmt").is_file(), "Private TeX format was not produced")
    maps = []
    for name in ("cm.map", "cmextra.map", "latxfont.map", "symbols.map", "lm.map"):
        path = Path(tex_command(["kpsewhich", name], work, env))
        require(path.is_file(), "Installed font map is missing: "+name)
        maps.append(path.read_bytes())
    (work/"pdftex.map").write_bytes(b"\n".join(maps)+b"\n")


def compile_pdf(source_root, scratch, destination):
    work = Path(scratch)
    work.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(checked_file(source_root, "Report202.tex"), work/"Report202.tex")
    env = clean_environment(work)
    prepare_tex(work, env)
    # The command prefix suppresses dates, trailer IDs and path-bearing pdfTeX data.
    tex = r"\pdfinfoomitdate=1\pdftrailerid{}\pdfsuppressptexinfo=15\input{Report202.tex}"
    command = ["pdflatex", "-no-shell-escape", "-halt-on-error", "-interaction=batchmode",
               "-file-line-error", "-jobname=Report202", tex]
    previous = None
    stable = False
    for attempt in range(1, 6):
        try:
            result = subprocess.run(command, cwd=work, env=env, capture_output=True,
                                    timeout=180, check=False)
        except (OSError, subprocess.SubprocessError) as exc:
            raise BuildError("pdflatex failed to run") from exc
        if result.returncode:
            log = (work/"Report202.log").read_text(encoding="utf-8", errors="replace") if (work/"Report202.log").exists() else ""
            raise BuildError("PDF compilation failed; final log lines:\n"+"\n".join(log.splitlines()[-35:]))
        pdf = (work/"Report202.pdf").read_bytes()
        require(pdf.startswith(b"%PDF-"), "Compiler did not produce a PDF")
        if attempt >= 3 and pdf == previous:
            stable = True
            break
        previous = pdf
    require(stable, "PDF did not stabilize after five deterministic compilation passes")
    log = (work/"Report202.log").read_text(encoding="utf-8", errors="replace")
    require("There were undefined references" not in log and "There were undefined citations" not in log and
            "Rerun to get cross-references right" not in log, "Unresolved references or citations in PDF")
    Path(destination).write_bytes(pdf)


def deterministic_zip(root, archive):
    root, archive = Path(root), Path(archive)
    require(not archive.exists() and not archive.is_symlink(), "Archive destination already exists")
    require(not archive.resolve().is_relative_to(root.resolve()), "Archive must be outside the package directory")
    archive.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_STORED, allowZip64=True) as zf:
        zf.comment = b""
        for name in PUBLIC_FILES:
            info = zipfile.ZipInfo("Report202/"+name, date_time=ZIP_DATE)
            info.compress_type = zipfile.ZIP_STORED
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.internal_attr = 0
            info.extra = b""
            info.comment = b""
            zf.writestr(info, checked_file(root, name).read_bytes())
    return sha256(archive.read_bytes())


def build(source, output, archive, initialize=False):
    source, output, archive = Path(source).resolve(), Path(output).absolute(), Path(archive).absolute()
    require(output != source and not source.is_relative_to(output.resolve()) and not output.resolve().is_relative_to(source),
            "Output and source package must be separate, non-nested directories")
    require(not output.exists() and not output.is_symlink(), "Output directory already exists; choose a fresh destination")
    require(not archive.exists() and not archive.is_symlink(), "Archive already exists; choose a fresh destination")
    require(not archive.resolve().is_relative_to(output.resolve()), "Archive must be outside output package")
    require(not archive.resolve().is_relative_to(source), "Archive must be outside the source package")
    if initialize:
        for name in SOURCE_FILES: checked_file(source, name)
        banner = engine_banner()
    else:
        validate_package(source, check_toolchain=True)
        banner = strict_json(source/SOURCE_MANIFEST)["pdf_engine_banner"]
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="report202-build-", dir=output.parent) as temp:
        temporary = Path(temp)
        staged = temporary/"package"
        staged.mkdir()
        for name in SOURCE_FILES:
            destination = staged/name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(checked_file(source, name), destination)
        exact_receipt = run_checks(staged)
        compile_pdf(staged, temporary/"latex", staged/"Report202.pdf")
        (staged/"manifests").mkdir()
        (staged/SOURCE_MANIFEST).write_bytes(canonical_bytes(source_manifest(staged, banner)))
        (staged/PACKAGE_MANIFEST).write_bytes(canonical_bytes(package_manifest(staged)))
        validate_package(staged)
        if not initialize:
            for name in PUBLIC_FILES:
                require((staged/name).read_bytes() == checked_file(source, name).read_bytes(),
                        f"Byte-for-byte replay mismatch: {name}")
        shutil.move(str(staged), output)
    digest = deterministic_zip(output, archive)
    return {"status": "PASS", "public_members": len(PUBLIC_FILES),
            "pdf_sha256": sha256((output/"Report202.pdf").read_bytes()),
            "zip_sha256": digest, "exact_replay": exact_receipt,
            "identical_to_input_members": not initialize}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Fresh directory for the rebuilt public package")
    parser.add_argument("--archive", type=Path, help="Fresh ZIP path; defaults to OUTPUT.zip")
    parser.add_argument("--validate-only", action="store_true", help="Validate strict manifests without running TeX or exact replay")
    parser.add_argument("--initialize", action="store_true", help="Maintainer: initialize manifests from the allowlisted sources")
    args = parser.parse_args()
    try:
        if args.validate_only:
            require(args.output is None and args.archive is None and not args.initialize,
                    "--validate-only cannot be combined with build arguments")
            result = validate_package(ROOT)
        else:
            require(args.output is not None, "Supply --output with a fresh directory path")
            archive = args.archive if args.archive is not None else args.output.with_name(args.output.name+".zip")
            result = build(ROOT, args.output, archive, initialize=args.initialize)
        print(json.dumps(result, sort_keys=True, indent=2))
    except (BuildError, OSError, ValueError) as exc:
        parser.exit(1, f"Build failed: {exc}\n")


if __name__ == "__main__":
    main()
