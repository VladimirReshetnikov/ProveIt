"""Recover batch 148 from Git and run its finite checks outside the checkout.

Includes the complete 4,000-choice grammar comparison and independent register
certificate checker. No proof assistant, network or unbounded search is used.
Delivered files are recovered unchanged; generated evidence stays in scratch.
"""
from __future__ import annotations

import argparse
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from zipfile import ZipFile


def main() -> None:
    if not __debug__:
        raise SystemExit("Run without -O/PYTHONOPTIMIZE: checks use assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    repo = next(p for p in Path(__file__).resolve().parents if (p / ".git").exists())
    scratch = Path(tempfile.mkdtemp(prefix="zfc-batch148-reproduce-"))
    raw = subprocess.check_output([
        "git", "show", "5e5603303d:docs/incoming/zfc_consistency_machine_report_20261016.zip"
    ], cwd=repo)
    with ZipFile(io.BytesIO(raw)) as zipped:
        for name in zipped.namelist():
            path = Path(name)
            if path.is_absolute() or ".." in path.parts:
                raise ValueError(f"Archive path escapes scratch: {name}")
        zipped.extractall(scratch / "package")
    root = scratch / "package/zfc_machine_research"
    print(f"Scratch: {scratch}", flush=True)
    if args.prepare_only:
        return
    jobs = [
        ("clausal", ["code/check_clausal_trace.py", "--output-dir", str(scratch / "clausal")]),
        ("prefix", ["code/clausal_trace.py", "--prefix", "1000"]),
        ("capture", ["code/capture_tagged_check.py"]),
        ("countermodel", ["code/equality_free_countermodel.py"]),
        ("grammar", ["code/search_full_grammar.py", "--archive", ".", "--output",
                     str(scratch / "grammar"), "--seeds", "1000"]),
        ("certificate", ["vendor/one_schema_machine/verify_rm_certificate.py", "--source",
            "vendor/ProveIt/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/prog/Dag254.v",
            "--candidate", str(scratch / "grammar/candidate_dag.json"),
            "--certificate", str(scratch / "grammar/rm_bisimulation.json")]),
    ]
    records = []
    for name, command in jobs:
        result = subprocess.run([sys.executable, "-B", *command], cwd=root,
                                capture_output=True, text=True)
        log = scratch / f"{name}.log"
        log.write_text(result.stdout + result.stderr)
        records.append(dict(check=name, command=command, returncode=result.returncode,
                            log=str(log)))
        (scratch / "runs.json").write_text(json.dumps(records, indent=2) + "\n")
        print(f"{name}: exit {result.returncode}", flush=True)
        if result.returncode:
            print(result.stdout + result.stderr, file=sys.stderr)
            raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
