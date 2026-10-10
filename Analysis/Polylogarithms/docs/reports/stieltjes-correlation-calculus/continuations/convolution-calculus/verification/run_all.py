"""Run the independent verification scripts and inspect their reported results.

The full run regenerates result JSON and the figure.  Quick mode preserves
the supplied numerical results by using a temporary directory.
These computations are diagnostics; the article supplies the analytic proofs.
"""
from __future__ import annotations

import argparse
from decimal import Decimal
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def run(name: str, *args: str) -> None:
    start = time.monotonic()
    print(f"Running {name} ...", flush=True)
    completed = subprocess.run(
        [sys.executable, str(HERE / name), *map(str, args)],
        cwd=ROOT, text=True, capture_output=True,
    )
    if completed.returncode:
        print(completed.stdout, end="")
        print(completed.stderr, end="", file=sys.stderr)
        raise SystemExit(completed.returncode)
    print(f"  completed in {time.monotonic()-start:.1f} s", flush=True)


def inspect_gamma(path: Path) -> None:
    data = json.loads(path.read_text())
    assert data["summary"]["all_checks_passed"], path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    run("exact_coefficients.py")
    run("exact_jet_polynomials.py")
    if args.quick:
        with tempfile.TemporaryDirectory(prefix="stieltjes_quick_") as directory:
            result = Path(directory) / "results_gamma_quick.json"
            run("check_gamma_correlations.py", "--quick", "--no-figure",
                "--results", str(result))
            inspect_gamma(result)
        print("Quick symbolic and numerical checks passed.")
        return

    for name in (
        "check_finite_parts.py", "check_reflected10.py",
        "check_gamma_correlations.py", "derivative_anomaly_check.py",
        "check_hankel_and_ladder.py",
    ):
        run(name)

    for filename, expected_count, tolerance in (
        ("results00.json", 11, "1e-50"),
        ("results10.json", 4, "1e-40"),
    ):
        records = json.loads((HERE / filename).read_text())
        assert len(records) == expected_count, filename
        assert all(Decimal(row["absolute_error"]) < Decimal(tolerance)
                   for row in records), filename
    inspect_gamma(HERE / "results_gamma.json")
    for filename in ("results_derivative_anomaly.json", "results_hankel_ladder.json"):
        assert json.loads((HERE / filename).read_text())["status"] == "passed", filename
    print("All supplied symbolic and numerical checks passed.")
    print("Numerical agreement is not an interval certificate.")


if __name__ == "__main__":
    main()
