"""Rebuild evidence and optionally the standalone PDF; no network required."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
CODE = ROOT / "code"


def run(name):
    result = subprocess.run([sys.executable, name], cwd=CODE, text=True,
                            capture_output=True, check=True)
    print(name + ": " + result.stdout.strip())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pdf", action="store_true")
    parser.add_argument("--check-manifest", action="store_true")
    args = parser.parse_args()
    if args.check_manifest:
        for line in (ROOT / "MANIFEST.sha256").read_text().splitlines():
            digest, name = line.split("  ", 1)
            actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            if actual != digest:
                raise ValueError("Checksum mismatch: " + name)
        print("Delivered checksum manifest verified.")
    for name in ["verify_scalar.py", "verify_semantics.py", "measure.py"]:
        run(name)
    cases = json.loads((CODE / "cli_cases.json").read_text())
    outcomes = []
    for optimized in [False, True]:
        for case in cases:
            command = [sys.executable]
            if optimized:
                command.append("-O")
            command.append(str(CODE / case["checker"]))
            result = subprocess.run(command, input=(CODE / case["path"]).read_text(),
                                    text=True, capture_output=True, timeout=30)
            accepted = result.returncode == 0 and result.stdout == "ACCEPT\n"
            ok = accepted == case["expected"]
            outcomes.append({"path": case["path"], "optimized": optimized,
                             "expected_accept": case["expected"], "passed": ok})
            if not ok:
                raise ValueError("Unexpected CLI result: " + case["path"])
    report = {"checks": len(outcomes), "passed": True, "results": outcomes}
    (CODE / "cli_verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print("CLI checks: " + str(len(outcomes)) + ", all passed.")
    if args.pdf:
        for _ in range(3):
            result = subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "report.tex"],
                cwd=ROOT, text=True, capture_output=True)
            if result.returncode:
                print(result.stdout)
                raise RuntimeError("PDF build failed")
        print("Built report.pdf from the standalone report.tex.")


if __name__ == "__main__":
    main()
