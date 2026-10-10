#!/usr/bin/env python3
"""Replay exact certificates, optionally including numerical diagnostics.

Usage from the archive root:
    python code/run_checks.py --fast
    python code/run_checks.py --full

The fast mode uses exact rational/symbolic algebra and integer interval
arithmetic. The full mode adds floating-point diagnostics, whose success
is never reported as a proof of a conjectural identity.
"""
import argparse
import importlib.util
import importlib.metadata
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def load_module(name, relative):
    spec = importlib.util.spec_from_file_location(name, ROOT/relative)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def execute(relative, *arguments):
    print(f"Running {relative}", flush=True)
    process = subprocess.run([sys.executable, str(ROOT/relative), *arguments],
                             cwd=ROOT, capture_output=True, text=True)
    if process.returncode:
        print(process.stdout)
        print(process.stderr, file=sys.stderr)
        raise RuntimeError(f"{relative} failed with exit code {process.returncode}")
    return process.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--fast", action="store_true")
    group.add_argument("--full", action="store_true")
    args = parser.parse_args()
    start = time.monotonic()
    report = {
        "status": "RUNNING",
        "mode": "full" if args.full else "fast",
        "python": platform.python_version(),
        "dependencies": {name: importlib.metadata.version(name)
                         for name in ["mpmath", "sympy", "numpy", "matplotlib"]},
        "scope": "Exact certificates and, in full mode, independent numerical diagnostics; not a proof assistant formalization."
    }
    execute("code/shuffle_certificates.py", "--max-weight", "9",
            "--output", "data/shuffle_verification.json")
    shuffle = json.loads((ROOT/"data/shuffle_verification.json").read_text())
    report["shuffle"] = {key: shuffle[key] for key in [
        "status", "normal_forms_reexpanded", "bigraded_sectors_checked"]}

    print("Running exact depth and ladder coefficient checks", flush=True)
    depth = load_module("depth_exact", "code/depth/verify_depth.py")
    ladders = load_module("ladder_exact", "code/ladders/verify_ladders.py")
    report["depth_exact"] = depth.exact_checks()
    report["ladders_exact"] = ladders.exact_checks()

    certificate_path = ROOT/"code/moments/cubic_certificate.json"
    expected = json.loads(certificate_path.read_text())
    execute("code/moments/certify_cubic.py", "--order", "360", "--digits", "130")
    actual = json.loads(certificate_path.read_text())
    if actual != expected:
        raise AssertionError("The exact cubic certificate differs from the shipped reference.")
    report["cubic_certificate"] = {
        "reference_reproduced_exactly": True,
        "common_decimal_digits": actual["common_decimal_digits"],
        "width_upper": actual["width_upper"],
        "arithmetic": actual["arithmetic"]
    }
    report["numerical_programs_completed"] = []
    if args.full:
        numerical = [
            ("code/depth/verify_depth.py", []),
            ("code/depth/verify_mixed.py", []),
            ("code/ladders/verify_ladders.py",
             ["--digits", "100", "200", "--output", "code/ladders/verification.json"]),
            ("code/verify_s4_candidate.py", []),
            ("code/moments/verify_moments.py", []),
            ("article/figures/make_moment_figure.py", [])
        ]
        for program, arguments in numerical:
            execute(program, *arguments)
            report["numerical_programs_completed"].append(program)
    report["status"] = "PASS"
    report["elapsed_seconds"] = round(time.monotonic()-start, 3)
    output = ROOT/"data"/("validation_full.json" if args.full else "validation_fast.json")
    output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "status": report["status"], "mode": report["mode"],
        "normal_forms": shuffle["normal_forms_reexpanded"],
        "exact_ladder_checks": report["ladders_exact"]["passed"],
        "certified_common_digits": actual["common_decimal_digits"],
        "numerical_programs_completed": len(report["numerical_programs_completed"]),
        "elapsed_seconds": report["elapsed_seconds"],
        "report": str(output.relative_to(ROOT))
    }, indent=2))


if __name__ == "__main__":
    main()
