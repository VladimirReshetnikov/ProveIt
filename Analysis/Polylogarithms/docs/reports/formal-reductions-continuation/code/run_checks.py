#!/usr/bin/env python3
"""Replay the article's finite exact checks and numerical diagnostics.

No result of this program is a proof of numerical period independence.
The general theorems are proved in the accompanying article. Exact
arithmetic checks and floating-point diagnostics are identified separately.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
CODE = ROOT / "code"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "data")
    parser.add_argument("--skip-numeric", action="store_true",
                        help="Skip the angular numerical root diagnostic; J checks still include quadrature.")
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    tasks = [
        ("gaussian_ranks", "exact rational and integer arithmetic", "full_gaussian_rank.py", [], "full_gaussian_rank_results.json"),
        ("universal_lift", "exact rational and integer arithmetic", "universal_gaussian_lift.py", [], "universal_gaussian_lift_results.json"),
        ("lerch_certificates", "exact rational intervals and outward integer bounds", "verify_lerch_boundary.py", [], "lerch_boundary_certificates.json"),
        ("herglotz", "exact group algebra; independent floating-point quadrature", "verify_j.py", [], "verification_j.json"),
        ("angular_ten", "exact symbolic coefficients and Fourier residual", "derive_angular.py", ["--cutoff", "2/13"], "angular_coefficients.json"),
        ("angular_eleven", "exact symbolic coefficients and Fourier residual", "derive_angular.py", ["--cutoff", "4/27"], "angular_eleven.json"),
        ("angular_twelve", "exact symbolic coefficients and Fourier residual", "derive_angular.py", ["--cutoff", "1/7"], "angular_audit_coefficients.json"),
        ("angular_extended", "exact symbolic coefficients and Fourier residual", "derive_angular.py", ["--cutoff", "1/10"], "angular_extended.json"),
        ("angular_divergence", "exact rational coefficient polynomials; symbolic trigonometric checks", "check_angular_divergence.py", [], "angular_divergence_checks.json"),
    ]
    if not args.skip_numeric:
        tasks.append(("angular_numerical", "floating-point diagnostic with an analytic Fourier-tail bound", "check_angular.py", [], "angular_numeric.json"))

    def run(task):
        name, kind, script, options, destination = task
        command = [sys.executable, str(CODE / script), *options, "--output", str(out / destination)]
        start = time.monotonic()
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        record = {
            "name": name, "kind": kind, "script": "code/" + script,
            "script_sha256": sha256(CODE / script),
            "arguments": options + ["--output", "data/" + destination],
            "return_code": result.returncode,
            "elapsed_seconds": round(time.monotonic() - start, 3),
            "output": "data/" + destination,
        }
        if result.returncode == 0 and (out / destination).exists():
            record["output_sha256"] = sha256(out / destination)
        else:
            record["stdout_tail"] = result.stdout[-6000:]
            record["stderr_tail"] = result.stderr[-6000:]
        return record

    started = datetime.now(timezone.utc).isoformat()
    records = []
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as executor:
        futures = {executor.submit(run, task): task[0] for task in tasks}
        for future in as_completed(futures):
            record = future.result()
            records.append(record)
            print(("PASS" if record["return_code"] == 0 else "FAIL") + " " + record["name"], flush=True)
    records.sort(key=lambda item: item["name"])
    versions = {}
    for package in ("sympy", "mpmath", "matplotlib"):
        try:
            versions[package] = importlib.metadata.version(package)
        except importlib.metadata.PackageNotFoundError:
            versions[package] = None
    receipt = {
        "started_utc": started,
        "python": platform.python_version(),
        "packages": versions,
        "upstream_certificate_sha256": sha256(CODE / "upstream_stieltjes_certificate.py"),
        "all_checks_passed": all(item["return_code"] == 0 for item in records),
        "checks": records,
        "scope": "Finite exact verifications and explicitly labeled numerical corroboration; see the article for the general proofs.",
    }
    (out / "validation_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("Wrote " + str(out / "validation_receipt.json"), flush=True)
    return 0 if receipt["all_checks_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
