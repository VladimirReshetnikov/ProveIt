#!/usr/bin/env python3
"""Replay all packaged checks; numerical diagnostics are not certificates."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import time
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = [
    "verify_invariant_germs.py", "verify_contacts.py",
    "verify_spectral.py", "verify_rays.py",
    "verify_cubic_digamma.py", "verify_cubic_completion.py",
    "verify_two_exponent.py", "verify_slice_primitives.py",
    "review_tornheim_rays.py", "verify_s6_target.py",
]


def run(name):
    started = time.monotonic()
    script = ROOT / "code" / name
    proc = subprocess.run([sys.executable, str(script)], cwd=ROOT,
                          text=True, capture_output=True, check=False)
    log = ROOT / "results" / (script.stem + "_run.log")
    log.write_text(proc.stdout + proc.stderr)
    return {
        "script": name, "exit_code": proc.returncode,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "script_sha256": hashlib.sha256(script.read_bytes()).hexdigest(),
        "log": str(log.relative_to(ROOT)),
    }


def validate_outputs():
    read = lambda name: json.loads((ROOT / "results" / name).read_text())
    mp.mp.dps = 80
    checks = []

    def check(name, value):
        checks.append({"name": name, "passed": bool(value)})

    check("exact invariant checks",
          read("invariant_germs_verification.json")["all_passed"])
    check("contact checks", read("contacts_verification.json")["all_passed"])
    check("ray symbolic review",
          all(row["pass"] for row in read("tornheim_peer_review.json")))
    cube = read("cubic_results.json")
    check("cubic independent representations",
          abs(mp.mpf(cube["cubic_residual"])) < mp.mpf("1e-32"))
    check("first diagonal derivative",
          abs(mp.mpf(cube["T1_residual"])) < mp.mpf("1e-38"))
    check("second diagonal derivative",
          abs(mp.mpf(cube["T2_residual"])) < mp.mpf("1e-38"))
    harmonic = read("two_exponent_verification.json")
    errors = [mp.mpf(e) for row in harmonic["cases"]
              for e in row["absolute_errors"].values()]
    check("harmonic Laurent extraction", max(errors) < mp.mpf("1e-40"))
    check("harmonic tail refinement",
          mp.mpf(harmonic["tail_repeat_difference"]) < mp.mpf("1e-48"))
    ray = read("ray_results.json")
    check("numerical ray derivatives",
          max(mp.mpf(e) for row in ray["records"]
              for e in row["absolute_errors"]) < mp.mpf("1e-35"))
    return checks


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=3)
    args = parser.parse_args()
    (ROOT / "results").mkdir(exist_ok=True)
    records = []
    with ThreadPoolExecutor(max_workers=max(1, args.workers)) as pool:
        pending = {pool.submit(run, s): s for s in SCRIPTS}
        for future in as_completed(pending):
            record = future.result()
            records.append(record)
            print(json.dumps(record), flush=True)
    records.sort(key=lambda r: SCRIPTS.index(r["script"]))
    exit_ok = all(r["exit_code"] == 0 for r in records)
    checks = validate_outputs() if exit_ok else []
    passed = exit_ok and all(c["passed"] for c in checks)
    out = {"all_passed": passed,
           "qualification": "Exact symbolic checks and floating-point diagnostics; no interval certificate.",
           "runs": records, "output_checks": checks}
    (ROOT / "results" / "replay_summary.json").write_text(
        json.dumps(out, indent=2) + "\n")
    print(json.dumps({"all_passed": passed, "scripts": len(records),
                      "output_checks": len(checks)}), flush=True)
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
