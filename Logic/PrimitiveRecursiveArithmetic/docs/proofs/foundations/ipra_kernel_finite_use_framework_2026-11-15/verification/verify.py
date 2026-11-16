#!/usr/bin/env python3
"""Reproducible verification driver for the KFFU research package."""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def run(cmd: list[str], *, env: dict[str, str] | None = None) -> tuple[int, str]:
    proc = subprocess.run(
        cmd,
        cwd=ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    return proc.returncode, proc.stdout


def strip_lean_comments(text: str) -> str:
    """Remove nested Lean block comments and line comments for token auditing."""
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth:
            i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1:
                break
            out.append("\n")
            i = j + 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def main() -> int:
    report: list[str] = []
    ok = True

    report.append("KFFU verification report")
    report.append("========================")
    report.append("")

    env = dict(**__import__("os").environ)
    env["PYTHONPATH"] = str(ROOT / "code")
    rc, output = run([sys.executable, "code/test_kffu.py"], env=env)
    (ROOT / "verification/test_output.txt").write_text(output, encoding="utf-8")
    report.append(f"Python unit tests: {'PASS' if rc == 0 else 'FAIL'}")
    report.append("  9 exact-arithmetic and finite-graph tests expected.")
    ok &= rc == 0

    rc_compile, output_compile = run(
        [sys.executable, "-m", "py_compile", "code/kffu.py", "code/test_kffu.py", "code/generate_lean_schedule.py"]
    )
    report.append(f"Python bytecode compilation: {'PASS' if rc_compile == 0 else 'FAIL'}")
    if output_compile:
        report.append("  " + output_compile.strip().replace("\n", "\n  "))
    ok &= rc_compile == 0

    # Regeneration determinism.
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        sched = tmp / "GeneratedSchedule.lean"
        rc_gen, out_gen = run(
            [sys.executable, "code/generate_lean_schedule.py", "examples/contract_dag.json", str(sched)]
        )
        schedule_match = rc_gen == 0 and sched.read_bytes() == (ROOT / "examples/GeneratedSchedule.lean").read_bytes()
        report.append(f"Lean schedule regeneration: {'PASS' if schedule_match else 'FAIL'}")
        if out_gen:
            report.append("  " + out_gen.strip().replace("\n", "\n  "))
        ok &= schedule_match

        cubic = tmp / "cubic.json"
        code = (
            "from fractions import Fraction; from kffu import cubic_bisection_certificate; "
            "import json, pathlib; "
            f"pathlib.Path(r'{cubic}').write_text(json.dumps(cubic_bisection_certificate(Fraction(7,3),12), indent=2)+'\\n')"
        )
        rc_cubic, out_cubic = run([sys.executable, "-c", code], env=env)
        cubic_match = rc_cubic == 0 and cubic.read_bytes() == (ROOT / "examples/cubic_certificate.json").read_bytes()
        report.append(f"Cubic certificate regeneration: {'PASS' if cubic_match else 'FAIL'}")
        if out_cubic:
            report.append("  " + out_cubic.strip().replace("\n", "\n  "))
        ok &= cubic_match

    # JSON well-formedness.
    json_files = sorted(ROOT.glob("metadata/*.json")) + sorted(ROOT.glob("examples/*.json"))
    json_ok = True
    for path in json_files:
        try:
            json.loads(path.read_text(encoding="utf-8"))
        except Exception as exc:  # pragma: no cover - diagnostic path
            json_ok = False
            report.append(f"  malformed JSON {path.relative_to(ROOT)}: {exc}")
    report.append(f"JSON parse audit ({len(json_files)} files): {'PASS' if json_ok else 'FAIL'}")
    ok &= json_ok

    # Lean placeholder/static target audit.
    lean_report: list[str] = []
    lean_ok = True
    total_embedded = 0
    for path in sorted((ROOT / "lean").glob("*.lean")):
        raw = path.read_text(encoding="utf-8")
        code_only = strip_lean_comments(raw)
        forbidden = []
        for token in (r"\bsorry\b", r"\badmit\b", r"\baxiom\b"):
            if re.search(token, code_only):
                forbidden.append(token.strip("\\b"))
        embedded = code_only.count("⊢[PRAAx]")
        total_embedded += embedded
        status = "PASS" if not forbidden else "FAIL"
        lean_report.append(
            f"{path.name}: {status}; embedded-judgment occurrences={embedded}; forbidden={forbidden or 'none'}"
        )
        lean_ok &= not forbidden
    lean_report.append(f"Total embedded-judgment occurrences: {total_embedded}")
    lean_report.append(f"Lean executable available: {'yes' if shutil.which('lean') else 'no'}")
    (ROOT / "verification/static_lean_audit.txt").write_text("\n".join(lean_report) + "\n", encoding="utf-8")
    report.append(f"Lean placeholder audit: {'PASS' if lean_ok else 'FAIL'}")
    report.append(f"Lean typecheck in this runtime: {'AVAILABLE' if shutil.which('lean') else 'NOT AVAILABLE'}")
    report.append("  Absence of a local Lean executable means no typechecking claim is made.")
    ok &= lean_ok

    # PDF/text audit.
    pdf = ROOT / "paper/ipra_kernel_finite_use_framework.pdf"
    tex = ROOT / "paper/ipra_kernel_finite_use_framework.tex"
    pdf_ok = pdf.exists() and pdf.stat().st_size > 100_000 and tex.exists()
    report.append(f"PDF and TeX existence/size: {'PASS' if pdf_ok else 'FAIL'}")
    ok &= pdf_ok
    if pdf_ok and shutil.which("pdftotext"):
        rc_text, text_output = run(["pdftotext", str(pdf), "-"])
        markers = [
            "Kernel-Facing Finite-Use Framework",
            "Finite DAG compilation",
            "Cubic finite-use certificate",
            "Lean formalization architecture",
        ]
        text_ok = rc_text == 0 and all(marker in text_output for marker in markers)
        report.append(f"PDF text marker audit: {'PASS' if text_ok else 'FAIL'}")
        ok &= text_ok

    # No control bytes in authored text/code files.
    control_ok = True
    for pattern in ("*.md", "*.tex", "*.lean", "*.py", "*.json", "*.csv", "*.toml"):
        for path in ROOT.rglob(pattern):
            data = path.read_bytes()
            bad = [b for b in data if b < 32 and b not in (9, 10, 13)]
            if bad:
                control_ok = False
                report.append(f"  control byte in {path.relative_to(ROOT)}")
    report.append(f"Control-byte audit: {'PASS' if control_ok else 'FAIL'}")
    ok &= control_ok

    report.append("")
    report.append("Overall: " + ("PASS" if ok else "FAIL"))
    report.append("")
    report.append("Scope note: Python tests validate finite reference algorithms only.  The generic Lean")
    report.append("files are statically placeholder-free but remain uncompiled until checked in the pinned")
    report.append("Lean 4.32.0/Mathlib environment with the surrounding ConciseIPRA library.")

    path = ROOT / "verification/verification_report.txt"
    path.write_text("\n".join(report) + "\n", encoding="utf-8")
    print(path.read_text(encoding="utf-8"), end="")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
