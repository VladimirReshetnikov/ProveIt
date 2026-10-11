#!/usr/bin/env python3
"""Replay the four independent mathematical diagnostics from any directory.

Each script writes its own JSON. A nonzero return code stops this runner.
These computations accompany analytic proofs; they are not proof-assistant
formalizations or certified interval enclosures.
"""
from __future__ import annotations

import json
import subprocess
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    reports = []
    for name in ("harmonic", "dougall", "twists", "collisions"):
        script = ROOT / "code" / f"verify_{name}.py"
        target = ROOT / "results" / f"{name}.json"
        started = time.monotonic()
        print(f"Running {name} diagnostics", flush=True)
        subprocess.run(
            [sys.executable, str(script), "--output", str(target)],
            cwd=ROOT,
            check=True,
        )
        # Confirm a real, parseable record was produced. Threshold assertions,
        # where appropriate, are inside the individual verification scripts.
        with target.open(encoding="utf-8") as handle:
            json.load(handle)
        reports.append({
            "suite": name,
            "output": str(target.relative_to(ROOT)),
            "exit_code": 0,
            "elapsed_seconds": round(time.monotonic() - started, 3),
        })
    result = {
        "all_scripts_completed": True,
        "interpretation": (
            "Exact finite symbolic checks and floating-point diagnostics; "
            "analytic proofs are in the article. Collision residuals test "
            "an asymptotic expansion and are not expected to vanish at "
            "positive epsilon."
        ),
        "runs": reports,
    }
    (ROOT / "results" / "replay_summary.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    print("All four scripts completed; results/replay_summary.json written.", flush=True)


if __name__ == "__main__":
    main()
