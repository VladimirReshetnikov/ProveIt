#!/usr/bin/env python3
"""Verify the sealed package and replay exact arithmetic, mutations, and optional PDF."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
from integrity import validate

ROOT = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise RuntimeError("REPLAY_FAILURE " + message)

def command(script, optimized, *arguments):
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1", TZ="UTC", LC_ALL="C")
    result = subprocess.run([sys.executable] + (["-O"] if optimized else []) +
                            [str(ROOT / script)] + list(arguments),
                            cwd=ROOT, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, check=False, timeout=600)
    require(result.returncode == 0,
            script + " failed: " + result.stderr.decode(errors="replace")[-3000:])
    require(not result.stderr, script + " wrote unexpected stderr")
    return result.stdout

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-pdf", action="store_true")
    args = parser.parse_args()
    integrity = validate(ROOT)
    records = []
    for optimized in [False, True]:
        output = command("checks/validate.py", optimized)
        require(output == (ROOT / "checks/results.json").read_bytes(),
                "exact results differ from archived results")
        exact = json.loads(output)
        require(exact["status"] == "PASS", "exact checker did not pass")
        mutations = command("checks/mutation_campaign.py", optimized)
        require(mutations == (ROOT / "checks/mutation_results.json").read_bytes(),
                "mutation results differ from archived results")
        campaign = json.loads(mutations)
        require(campaign["status"] == "PASS", "mutation campaign did not pass")
        attacks = command("integrity_tests.py", optimized)
        require(attacks == (ROOT / "integrity_results.json").read_bytes(),
                "integrity-test results differ from archived results")
        checks = json.loads(attacks)
        require(checks["status"] == "PASS", "integrity attacks did not pass")
        records.append({"optimized": optimized, "exact_status": exact["status"],
                        "named_mathematical_or_schema_mutants": campaign["named_cases"],
                        "rejected_mutant_runs": campaign["rejected_runs"],
                        "rejected_integrity_mutants": checks["rejected"]})
    pdf = {"status": "NOT_REQUESTED"}
    if args.build_pdf:
        with tempfile.TemporaryDirectory(prefix="report114-clean-pdf-replay-") as temporary:
            first, second = [Path(temporary) / name for name in ["first.pdf", "second.pdf"]]
            command("build_pdf.py", False, "--output", str(first))
            command("build_pdf.py", False, "--output", str(second))
            content = first.read_bytes()
            require(content == second.read_bytes(), "clean PDF builds differ")
            require(content == (ROOT / "report114.pdf").read_bytes(),
                    "rebuilt PDF differs from archived PDF; check recorded TeX toolchain")
            pdf = {"status": "PASS", "clean_builds": 2, "byte_identical": True,
                   "sha256": sha256(content).hexdigest()}
    require(validate(ROOT) == integrity, "package changed during replay")
    print(json.dumps({"status": "PASS", "integrity": integrity,
                      "runs": records, "pdf": pdf, "package_unchanged": True},
                     indent=2, sort_keys=True))

if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError, subprocess.TimeoutExpired) as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(2)
