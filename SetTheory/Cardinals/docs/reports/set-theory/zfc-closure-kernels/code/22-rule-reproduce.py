#!/usr/bin/env python3
"""Regenerate finite diagnostics and certificates; optionally build the PDF.

No command here starts the unbounded consistency search. Python 3.10+ and
its standard library suffice for diagnostics. --pdf additionally requires
latexmk, pdflatex, and the LaTeX packages listed by report.tex.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent


def run():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdf", action="store_true", help="also rebuild report.pdf")
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Assertions are required; do not use Python -O.")
    jobs = [
        ("check_debruijn_kernel.py", "debruijn_diagnostics.json"),
        ("check_wrapper_transport.py", "wrapper_transport_diagnostics.json"),
        ("check_protected_rule.py", "protected_rule_diagnostics.json"),
        ("closure_rule_checks.py", "closure_rule_results.json"),
        ("protected_rule_checks.py", "protected_rule_results.json"),
        ("check_integration.py", "integration_results.json"),
    ]
    started = time.monotonic()
    for script, output in jobs:
        result = subprocess.run(
            [sys.executable, str(ROOT / "code" / script), "--output", str(ROOT / "data" / output)],
            check=True, capture_output=True, text=True,
        )
        data = json.loads((ROOT / "data" / output).read_text())
        if data["status"] != "PASS":
            raise RuntimeError(f"Diagnostic did not pass: {script}")
        print(f"PASS {script}", flush=True)
    for presentation, name in [
        ("protected", "empty_closure_certificate.json"),
        ("rule", "empty_basic_closure_certificate.json"),
    ]:
        subprocess.run(
            [sys.executable, str(ROOT / "code" / "make_empty_certificate.py"),
             str(ROOT / "data" / name), "--presentation", presentation],
            check=True, capture_output=True, text=True,
        )
        checked = subprocess.run(
            [sys.executable, str(ROOT / "code" / "rule_search.py"), str(ROOT / "data" / name)],
            check=True, capture_output=True, text=True,
        )
        state = json.loads(checked.stdout)
        if not state["accepted"] or state["refutation"] or state["lines"] != 76:
            raise RuntimeError(f"Unexpected positive certificate result: {name}")
        print(f"PASS {name}: 76 lines, theorem demonstration", flush=True)
    if args.pdf:
        subprocess.run(
            ["latexmk", "-pdf", "-silent", "-interaction=nonstopmode",
             "-halt-on-error", "-file-line-error", "report.tex"],
            cwd=ROOT, check=True,
        )
        print("PASS report.pdf rebuilt", flush=True)
    print(f"All requested checks completed in {time.monotonic() - started:.1f}s.")


if __name__ == "__main__":
    run()
