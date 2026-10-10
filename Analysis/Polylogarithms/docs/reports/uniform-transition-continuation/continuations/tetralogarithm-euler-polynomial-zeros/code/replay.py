#!/usr/bin/env python3
"""Replay the finite checks supplied with the research article.

Default: exact algebra, rational root isolation, rigorous finite sign
enclosures, and the tetralogarithm branch audit. With --numerical, also
rerun the larger non-certified Euler quadratures and optimizer table.
The infinite analytic theorems are proved in the article, not by this script.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

CODE = Path(__file__).resolve().parent
ROOT = CODE.parent
DATA = ROOT / "data"


def run(name: str, arguments: list[str]) -> dict:
    started = time.monotonic()
    process = subprocess.run(
        [sys.executable, *arguments],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    log = DATA / (name + "_replay.log")
    log.write_text(process.stdout + process.stderr, encoding="utf-8")
    if process.returncode:
        print(process.stdout)
        print(process.stderr, file=sys.stderr)
        raise RuntimeError(f"{name} failed with exit code {process.returncode}")
    receipt = {
        "name": name,
        "status": "PASS",
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "log": str(log.relative_to(ROOT)),
    }
    print(f"{name}: PASS", flush=True)
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--numerical", action="store_true")
    args = parser.parse_args()
    DATA.mkdir(exist_ok=True)
    checks = [
        run("tetralogarithm", [str(CODE / "verify_tetra.py")]),
        run("fractional", [
            str(CODE / "verify_fractional.py"),
            "--output", str(DATA / "fractional_checks.json"),
        ]),
        run("fractional_threshold", [
            str(CODE / "verify_fractional_threshold.py"),
            "--output", str(DATA / "fractional_threshold_certificate.json"),
        ]),
        run("polynomial_mesh", [
            str(CODE / "verify_polynomial_mesh.py"),
            "--output", str(CODE / "polynomial_mesh_certificates.json"),
        ]),
    ]
    spec = importlib.util.spec_from_file_location(
        "late_euler_verifier", CODE / "verify_late_euler.py")
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    algebra = module.symbolic_checks()
    assert all(algebra.values())
    checks.append({
        "name": "late_euler_symbolic",
        "status": "PASS",
        "checks": algebra,
    })
    print("late_euler_symbolic: PASS", flush=True)
    if args.numerical:
        checks.append(run("late_euler_numerical", [
            str(CODE / "verify_late_euler.py"), "--optimizers",
            "--output-dir", str(DATA),
        ]))
    watched = [
        CODE / "verify_tetra.py",
        CODE / "tetralogarithm_certificate.json",
        CODE / "verify_fractional.py",
        CODE / "verify_fractional_threshold.py",
        CODE / "verify_polynomial_mesh.py",
        CODE / "verify_late_euler.py",
    ]
    result = {
        "status": "PASS",
        "python_version": platform.python_version(),
        "scope": (
            "Finite exact checks plus a numerical branch audit. "
            "The analytic proofs are in the article. Larger Euler "
            "quadratures run only when --numerical is passed."
        ),
        "larger_numerical_diagnostics_rerun": args.numerical,
        "checks": checks,
        "input_sha256": {
            str(path.relative_to(ROOT)):
                hashlib.sha256(path.read_bytes()).hexdigest()
            for path in watched
        },
    }
    (DATA / "verification_receipt.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("All requested checks passed.")


if __name__ == "__main__":
    main()
