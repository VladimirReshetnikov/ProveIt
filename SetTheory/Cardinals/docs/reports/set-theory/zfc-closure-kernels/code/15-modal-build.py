#!/usr/bin/env python3
"""Build the report, run the delivered audits, or rebuild the ZIP.

Python 3.10+; the PDF build also requires pdflatex and the LaTeX packages
listed in report.tex. No network is used. Dependency retrieval is a
separate explicit action: python3 machines/fetch_dependencies.py.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_json(script, output, *args):
    proc = subprocess.run(
        [sys.executable, str(HERE / script), *map(str, args)],
        cwd=HERE, text=True, capture_output=True, timeout=120,
    )
    if proc.returncode:
        raise RuntimeError(f"{script} failed:\n{proc.stderr}\n{proc.stdout}")
    result = json.loads(proc.stdout)
    RESULTS.mkdir(exist_ok=True)
    (RESULTS / output).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return {"script": script, "output": "results/" + output, "passed": True}


def checks(include_machines, repo):
    executed = [
        run_json("code/base3_codec.py", "base3-codec.json"),
        run_json("code/logic_audit.py", "logic-audit.json"),
        run_json("code/table_audit.py", "table-audit.json"),
    ]
    if include_machines:
        args = ["--repo", repo] if repo else []
        executed.append(run_json("machines/verify_candidates.py",
                                 "root-candidate-replay.json", *args))
        executed.append(run_json("code/modal_search.py", "modal-search.json", *args))
    result = {
        "checks": executed,
        "scope": "Executable audits; not a formal proof of the proposed machine endpoint.",
        "new_proof_assistant_build_performed": False,
    }
    (RESULTS / "build-checks.json").write_text(json.dumps(result, indent=2) + "\n",
                                             encoding="utf-8")
    return result


def build_pdf():
    engine = shutil.which("pdflatex")
    if not engine:
        raise RuntimeError("pdflatex is required. Install a standard TeX distribution.")
    epoch = int(datetime(2026, 10, 16, tzinfo=timezone.utc).timestamp())
    pdf_env = os.environ.copy()
    pdf_env["SOURCE_DATE_EPOCH"] = str(epoch)
    pdf_env["FORCE_SOURCE_DATE"] = "1"
    with tempfile.TemporaryDirectory(prefix="zfc-report-tex-") as tmp:
        out = Path(tmp)
        for pass_number in range(1, 4):
            proc = subprocess.run(
                [engine, "-no-shell-escape", "-interaction=nonstopmode",
                 "-halt-on-error", "-file-line-error",
                 "-output-directory=" + str(out), "report.tex"],
                cwd=HERE, env=pdf_env, text=True, capture_output=True, timeout=120,
            )
            if proc.returncode:
                tail = "\n".join(proc.stdout.splitlines()[-65:])
                raise RuntimeError(f"LaTeX pass {pass_number} failed:\n{tail}\n{proc.stderr}")
        log = (out / "report.log").read_text(errors="replace")
        unresolved = [line for line in log.splitlines()
                      if re.search(r"(undefined|multiply defined|Rerun to get)", line, re.I)]
        if unresolved:
            raise RuntimeError("Unresolved LaTeX references:\n" + "\n".join(unresolved))
        pdf = out / "report.pdf"
        shutil.copyfile(pdf, HERE / "report.pdf")
        boxes = [line for line in log.splitlines() if "Overfull" in line]
        record = {
            "pdf": "report.pdf",
            "passes": 3,
            "bytes": pdf.stat().st_size,
            "undefined_references": False,
            "overfull_boxes": boxes,
            "sha256": sha256(pdf),
            "engine": Path(engine).name,
        }
        RESULTS.mkdir(exist_ok=True)
        (RESULTS / "pdf-build.json").write_text(json.dumps(record, indent=2) + "\n",
                                               encoding="utf-8")
        print(json.dumps(record, indent=2))
        if boxes:
            print("Layout review required: overfull boxes are listed above.", file=sys.stderr)
        return record


def artifact_files():
    excluded_parts = {"__pycache__", "upstream", ".git", ".build"}
    excluded_suffixes = {".pyc", ".aux", ".log", ".out", ".toc", ".fls", ".fdb_latexmk", ".zip"}
    return sorted(
        p for p in HERE.rglob("*")
        if p.is_file()
        and not (set(p.relative_to(HERE).parts) & excluded_parts)
        and p.suffix not in excluded_suffixes
        and p.name != "MANIFEST.sha256"
    )


def build_archive():
    if not (HERE / "report.pdf").is_file():
        raise RuntimeError("Compile report.pdf with --pdf before building the archive.")
    entries = artifact_files()
    manifest = HERE / "MANIFEST.sha256"
    manifest.write_text("".join(
        f"{sha256(p)}  {p.relative_to(HERE).as_posix()}\n" for p in entries
    ), encoding="utf-8")
    entries.append(manifest)
    archive = HERE.parent / "zfc_small_machine_proposal.zip"
    fixed_time = (2026, 10, 16, 0, 0, 0)
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
        for path in sorted(entries):
            name = HERE.name + "/" + path.relative_to(HERE).as_posix()
            info = zipfile.ZipInfo(name, date_time=fixed_time)
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = (0o100644 << 16)
            zf.writestr(info, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED,
                        compresslevel=9)
    with zipfile.ZipFile(archive) as zf:
        broken = zf.testzip()
        if broken:
            raise RuntimeError("Archive CRC failure: " + broken)
        for path in entries:
            name = HERE.name + "/" + path.relative_to(HERE).as_posix()
            if zf.read(name) != path.read_bytes():
                raise RuntimeError("Archive byte mismatch: " + name)
    return {"archive": str(archive), "files": len(entries),
            "bytes": archive.stat().st_size, "sha256": sha256(archive)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checks", action="store_true", help="run the self-contained audits")
    parser.add_argument("--machines", action="store_true",
                        help="also replay source compilation and modal diagnostics")
    parser.add_argument("--repo", type=Path, help="matching ProveIt checkout or partial snapshot")
    parser.add_argument("--pdf", action="store_true", help="compile the PDF in three passes")
    parser.add_argument("--archive", action="store_true", help="rebuild hashes and ZIP archive")
    args = parser.parse_args()
    if not any((args.checks, args.machines, args.pdf, args.archive)):
        parser.print_help()
        return
    if not __debug__:
        raise SystemExit("Run without -O: the audit scripts require Python assertions.")
    if args.checks or args.machines:
        print(json.dumps(checks(args.machines, args.repo), indent=2))
    if args.pdf:
        build_pdf()
    if args.archive:
        print(json.dumps(build_archive(), indent=2))


if __name__ == "__main__":
    main()

