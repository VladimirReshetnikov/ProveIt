#!/usr/bin/env python3
"""Regenerate restricted allocation domains and verify finite Hall witnesses.

This does not prove a general TM lower bound. The fixed-reader/protected-row
allocation model is specified by allocate.py and its pinned reference inputs.
No solver is invoked for these three infeasible domain systems.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
EXPECTED = {
    "source157": (81, 75, 81, 75),
    "essential158": (26, 23, 24, 21),
    "layout158": (46, 38, 44, 36),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check(name, output):
    run = subprocess.run(
        [sys.executable, str(HERE / "allocate.py"), str(HERE / (name + ".json")),
         str(output), "--feasible-only"],
        text=True, capture_output=True,
    )
    require(run.returncode == 0, "Allocator failed: " + run.stderr)
    receipt = json.loads((output / "allocation.json").read_text())
    require(receipt["status"] == "HALL_OBSTRUCTION", "No Hall witness")
    domains = receipt["domains"]
    nodes = receipt["hall_nodes"]
    require(len(set(nodes)) == len(nodes), "Duplicate witness node")
    require(set(nodes) <= set(domains), "Unknown witness node")
    neighbors = set().union(*(set(domains[n]) for n in nodes))
    require(neighbors == set(receipt["hall_labels"]), "Wrong domain union")
    require(len(neighbors) < len(nodes), "Hall inequality does not fail")
    found = (receipt["new_nodes"], receipt["maximum_domain_matching"],
             len(nodes), len(neighbors))
    require(found == EXPECTED[name], "Unexpected regenerated cardinalities")
    return {
        "layout": name,
        "new_nodes": found[0],
        "maximum_matching": found[1],
        "hall_nodes": found[2],
        "hall_labels": found[3],
        "source_sha256": hashlib.sha256((HERE / (name + ".json")).read_bytes()).hexdigest(),
        "status": "REGENERATED_DOMAIN_AND_HALL_WITNESS_PASS",
        "scope": "Specified fixed-reader, protected-row, injective allocation only",
    }


if __name__ == "__main__":
    require(__debug__, "Run with Python assertions enabled")
    with tempfile.TemporaryDirectory(prefix="pa_hall_") as temp:
        receipts = [check(name, Path(temp) / name) for name in EXPECTED]
    print(json.dumps(receipts, indent=2))
