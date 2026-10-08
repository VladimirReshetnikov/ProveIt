"""Replay bundled A5 witnesses against their exact measured fixture inputs."""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
BUNDLE = HERE.parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--name", help="one fixture stem, such as conway; omitted replays every certificate")
    args = parser.parse_args()
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(BUNDLE / "implementation/fast"))
    from fastunknot import Diagram
    from fastunknot.finite_quotient_check import verify_certificate
    recorded = json.loads((HERE / "finite_quotient_benchmark.json").read_text())
    for row in recorded["fixtures"]:
        path = HERE / "fixtures" / (row["name"] + ".json")
        if hashlib.sha256(path.read_bytes()).hexdigest() != row["fixture_sha256"]:
            raise AssertionError("measured fixture bytes changed: " + row["name"])
    paths = sorted((HERE / "certificates").glob("*_certificate.json"))
    if args.name:
        paths = [path for path in paths if path.name == args.name + "_certificate.json"]
        if not paths:
            parser.error("no stored certificate for " + args.name)
    reports = []
    for path in paths:
        name = path.name.removesuffix("_certificate.json")
        diagram = Diagram.from_json(json.loads((HERE / "fixtures" / (name + ".json")).read_text()))
        checked = verify_certificate(diagram.pd, json.loads(path.read_text()))
        if not checked["valid"]:
            raise AssertionError(name + ": " + checked["reason"])
        reports.append({"name": name, "crossings": diagram.crossings, **checked})
    print(json.dumps({"status": "PASS", "recorded_fixture_hashes": len(recorded["fixtures"]),
                      "certificates_replayed": len(reports), "reports": reports}, indent=2))


if __name__ == "__main__":
    main()
