#!/usr/bin/env python3
"""Replay four finite demonstrations and record their outputs and source hashes.

This is an integration check, not an iPRA proof checker or a universal proof.
"""
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import platform
import subprocess
import sys
from time import perf_counter

ROOT = Path(__file__).resolve().parent
PROGRAMS = [
    ("code/compact_logic.py", "evidence/compact_logic_checks.json"),
    ("code/topology_demo.py", "evidence/topology_checks.json"),
    ("code/hilbert_solver.py", "evidence/hilbert_checks.json"),
    ("code/complex_jets.py", "evidence/complex_checks.json"),
]


def main():
    if sys.flags.optimize:
        raise SystemExit("Run without -O: the demonstration checks use assertions.")
    evidence = ROOT / "evidence"
    evidence.mkdir(exist_ok=True)
    summary = {
        "status": "running",
        "scope": "finite exact-arithmetic integration checks; not universal proofs or iPRA derivations",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "python_version": platform.python_version(),
        "programs": [],
    }
    started = perf_counter()
    try:
        for program, output in PROGRAMS:
            print(f"Running {program}", flush=True)
            begin = perf_counter()
            command = [sys.executable, program, "--output", output]
            result = subprocess.run(command, cwd=ROOT, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            record = {
                "program": program,
                "arguments": ["--output", output],
                "program_sha256": sha256((ROOT / program).read_bytes()).hexdigest(),
                "output": output,
                "returncode": result.returncode,
                "elapsed_seconds": round(perf_counter() - begin, 6),
            }
            summary["programs"].append(record)
            if result.returncode:
                record["diagnostic"] = result.stdout[-6000:]
                raise RuntimeError(f"{program} failed:\n{result.stdout}")
            output_bytes = (ROOT / output).read_bytes()
            data = json.loads(output_bytes)
            record["reported_status"] = data.get("status")
            record["output_sha256"] = sha256(output_bytes).hexdigest()
            if data.get("status") != "passed":
                raise RuntimeError(f"{program} did not report status 'passed'.")
            print(f"  passed ({record['elapsed_seconds']:.3f}s); wrote {output}", flush=True)
        summary["status"] = "passed"
    except Exception as error:
        summary["status"] = "failed"
        summary["error"] = str(error)
        raise
    finally:
        summary["elapsed_seconds"] = round(perf_counter() - started, 6)
        summary["finished_utc"] = datetime.now(timezone.utc).isoformat()
        (evidence / "integration_checks.json").write_text(
            json.dumps(summary, indent=2) + "\n")
    print("All four finite exact-arithmetic demonstrations passed.")


if __name__ == "__main__":
    main()
