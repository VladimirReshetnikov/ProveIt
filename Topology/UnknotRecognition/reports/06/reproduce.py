"""Regenerate example reports, environment metadata and the test transcript."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys

from unknot import Diagram, recognize
from unknot.patterns import BallPattern, classify_pattern


def main() -> int:
    root = Path(__file__).resolve().parent
    results = root / "results"
    results.mkdir(exist_ok=True)
    benchmarks = []
    for source in sorted((root / "examples").glob("*.json")):
        value = json.loads(source.read_text(encoding="utf-8"))
        if source.name.startswith("pattern-"):
            report = classify_pattern(BallPattern.from_json(value))
        else:
            report = recognize(Diagram.from_json(value), check_d_squared=True)
            benchmarks.append({"example": source.stem, "crossings": report["crossings"],
                               "status": report["status"],
                               "dimension": report["reduced_homology_dimension"],
                               "resolutions": report["resolutions"],
                               "generators": report["total_generators"],
                               "elapsed_seconds": report["elapsed_seconds"]})
        (results/source.name).write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    (results/"BENCHMARKS.json").write_text(json.dumps(benchmarks, indent=2)+"\n", encoding="utf-8")
    environment = {"python": sys.version, "platform": platform.platform(),
                   "external_knot_packages_used": [], "formal_proof_checked": False,
                   "benchmark_check_d_squared": True,
                   "benchmark_scope": "Single local runs, not a complexity proof"}
    notes = root.parent / "quasipolynomial-talk.pdf"
    if notes.is_file():
        environment["supplied_notes_sha256"] = hashlib.sha256(notes.read_bytes()).hexdigest()
    (results/"ENVIRONMENT.json").write_text(json.dumps(environment, indent=2)+"\n", encoding="utf-8")
    command = [sys.executable, "-m", "unittest", "discover", "-s", "tests", "-v"]
    completed = subprocess.run(command, cwd=root, capture_output=True, text=True)
    transcript = ("Command: python -m unittest discover -s tests -v\n"
                  + "Python: " + sys.version + "\n\n"
                  + completed.stdout + completed.stderr
                  + f"\nExit code: {completed.returncode}\n")
    (results/"TEST_RESULTS.txt").write_text(transcript, encoding="utf-8")
    print(transcript, end="")
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
