#!/usr/bin/env python3
"""Run the certificate verifier in isolated normal and optimized processes."""

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent
cases = {"certificate.json": None, **json.loads((ROOT / "negative_controls.json").read_text())}
outcomes = []
for optimized in (False, True):
    for name, rejection_reason in cases.items():
        command = [sys.executable, "-I", "-S", "-B"]
        if optimized:
            command.append("-O")
        command.extend([str(ROOT / "verify_certificate.py"), str(ROOT / name)])
        run = subprocess.run(command, capture_output=True, text=True, timeout=15)
        if rejection_reason is None:
            data = json.loads(run.stdout) if run.returncode == 0 else {}
            passed = (run.returncode == 0 and data.get("status") == "ACCEPT"
                      and data.get("induction_nodes") == 2
                      and data.get("theorems") == {
                          "orbit_conjugacy": [["W", ["S", ["v", "t"]], ["S", ["S", ["v", "n"]]]],
                                              ["S", ["W", ["v", "t"], ["S", ["v", "n"]]]]],
                          "predecessor_successor": [["W", ["S", ["v", "n"]], ["S", ["v", "n"]]], ["v", "n"]],
                          "predecessor_zero": [["W", ["0"], ["0"]], ["0"]],
                      })
        else:
            data = {}
            passed = run.returncode == 1 and rejection_reason in run.stderr and not run.stdout
        outcomes.append({"file": name, "optimized": optimized, "passed": passed,
                         "expected": "accept" if rejection_reason is None else "reject",
                         "details": data if data else run.stderr.strip()})

evidence = {"python": sys.version.split()[0], "executions": len(outcomes),
            "failed_checks": sum(not result["passed"] for result in outcomes),
            "results": outcomes,
            "scope": "Finite symbolic derivation verification in the explicitly stated schematic equational kernel; not a full iPRA formalization."}
(ROOT / "verification.json").write_text(json.dumps(evidence, indent=2) + "\n")
print(json.dumps({"executions": evidence["executions"], "failed_checks": evidence["failed_checks"]}))
raise SystemExit(bool(evidence["failed_checks"]))
