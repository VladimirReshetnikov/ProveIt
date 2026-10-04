#!/usr/bin/env python3
"""Run the article's checks in a temporary directory and compare snapshots."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--symbolic", action="store_true",
                        help="also run the independent SymPy check through order 8")
    args = parser.parse_args()
    base = Path(__file__).resolve().parent.parent
    data = base / "data"
    records = []
    logs = []

    with tempfile.TemporaryDirectory(prefix="oeis_verification_") as temp:
        temp = Path(temp)
        for script in (base / "code").glob("*.py"):
            if script.name != Path(__file__).name:
                shutil.copyfile(script, temp / script.name)

        def run(name, *options):
            start = time.monotonic()
            result = subprocess.run(
                [sys.executable, str(temp / name), *map(str, options)],
                cwd=temp, text=True, capture_output=True)
            duration = time.monotonic() - start
            logs.append(f"CHECK: {name} {' '.join(map(str, options))}\n"
                        f"EXIT: {result.returncode}\n"
                        f"{result.stdout}\n{result.stderr}\n")
            if result.returncode:
                raise RuntimeError(f"{name} failed:\n{result.stdout}\n{result.stderr}")
            records.append({"check": name, "status": "passed",
                            "seconds": round(duration, 3)})
            print("PASS:", name, flush=True)
            return result.stdout

        run("finite_certificate.py")
        run("verify_sign.py")
        run("independent_check.py")
        run("large_order.py")
        endpoint = json.loads(run("verify_complement.py"))
        assert endpoint == json.loads(
            (data / "endpoint_verification.json").read_text())
        for name in ("sign_verification.json", "independent_check.json",
                     "large_order_coefficients.json"):
            assert json.loads((temp / name).read_text()) == json.loads(
                (data / name).read_text()), name

        normalized = []
        for precision in (80, 120):
            target = temp / f"normalization_{precision}.json"
            run("normalization_diagnostics.py", "--max-index", 600,
                "--precision", precision, "--coefficients",
                data / "coefficients_600.txt", "--output", target)
            result = json.loads(target.read_text())
            assert result == json.loads(
                (data / target.name).read_text()), target.name
            normalized.append(result)
        assert normalized[0]["rows"] == normalized[1]["rows"]
        print("PASS: all displayed normalization digits agree", flush=True)

        if args.symbolic:
            run("asymptotic_check.py", 8)
            assert (temp / "asymptotic_check.txt").read_text() == (
                data / "asymptotic_check.txt").read_text()

    summary = {
        "status": "passed",
        "python_version": sys.version.split()[0],
        "optional_symbolic_check_included": args.symbolic,
        "checks": records,
        "recorded_exact_outputs_match": True,
        "normalization_80_and_120_displayed_digits_match": True,
        "scope": "Finite certificates and identities; infinite estimates are proved in the article.",
    }
    (data / "verification_run.txt").write_text("\n".join(logs))
    (data / "verification_summary.json").write_text(
        json.dumps(summary, indent=2) + "\n")
    print("All requested verification checks passed.", flush=True)


if __name__ == "__main__":
    main()
