#!/usr/bin/env python3
"""Reproduce all certificates without network access or a repository checkout."""
from pathlib import Path
import argparse
import json
import subprocess
import sys
import tempfile
import shutil
import time

ROOT = Path(__file__).resolve().parents[1]

def run(root):
    (root / "results").mkdir(parents=True, exist_ok=True)
    cases = [
        ("reconstruction", ["code/build_machine.py", "--check"]),
        ("universal_macro_inductions", ["code/check_macro_inductions.py"]),
        ("all_symbolic_instructions", ["code/check_instructions.py"]),
        ("independent_marking", ["code/check_marking_independent.py",
            "--baseline", "reference/prefix250_old.tm", "--candidate", "machine/zfc_prefix247_old.tm",
            "--output", "results/marking-independent.json"]),
        ("canonical_sparse_bootstrap", ["code/check_boot_canonical.py"]),
        ("independent_dense_bootstrap", ["code/check_boot_independent.py",
            "--source250", "reference/prefix250_old.tm", "--candidate-old", "machine/zfc_prefix247_old.tm",
            "--candidate-canonical", "machine/zfc_prefix247.tm", "--output", "results/bootstrap-independent.json"]),
        ("independent_literal_instructions", ["code/check_literal_instructions.py",
            "--program", "reference/Prog254.v", "--table", "machine/zfc_prefix247_old.tm",
            "--output", "results/literal-instructions.json"]),
    ]
    results = []
    for label, args in cases:
        began = time.monotonic()
        done = subprocess.run([sys.executable, "-B", *args], cwd=root,
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (root / "results" / (label + ".log")).write_text(done.stdout)
        row = dict(check=label, passed=done.returncode == 0,
                   seconds=time.monotonic()-began, exit_code=done.returncode)
        results.append(row)
        print(label, "PASS" if row["passed"] else "FAIL", flush=True)
        if not row["passed"]:
            print(done.stdout)
            break
    ok = len(results) == len(cases) and all(r["passed"] for r in results)
    summary = dict(status="PASS" if ok else "FAIL", results=results,
        python=sys.version.split()[0],
        scope="Exact construction, universal induction templates, all 8391 symbolic guards, independent finite replays.",
        new_lean_or_rocq_endpoint=False,
        note="The ordinary ZFC proof and mathematical semantics of the certificate rules are in report.tex/report.pdf.")
    (root / "results/verification.json").write_text(json.dumps(summary, indent=2)+"\n")
    if not ok:
        raise SystemExit(1)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--in-place", action="store_true", help="Refresh local results instead of checking a temporary copy.")
    args = ap.parse_args()
    if not __debug__:
        ap.error("Assertions are part of the certificates; do not use -O.")
    if args.in_place:
        run(ROOT)
    else:
        with tempfile.TemporaryDirectory(prefix="zfc-prefix247-check-") as temp:
            target = Path(temp) / "zfc-prefix247"
            shutil.copytree(ROOT, target, ignore=shutil.ignore_patterns("__pycache__", "*.pdf", "*.log", "*.aux", "*.out", "*.toc"))
            run(target)
        print("All seven checks passed. Delivered files were unchanged.")

if __name__ == "__main__":
    main()
