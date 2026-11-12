"""Focused public-boundary regression checks; not trusted by the checker."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "code" / "checker.py"


def main():
    specification = importlib.util.spec_from_file_location("gj_checker", CHECKER)
    checker = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(checker)
    cases = json.loads((ROOT / "tests" / "certificates.json").read_text())["cases"]
    results = []
    for case in cases:
        try:
            accepted = checker.verify(copy.deepcopy(case["packet"]))
        except Exception:
            accepted = False
        if accepted != case["accept"]:
            raise RuntimeError("In-process mismatch: " + case["name"])
        for optimized in (False, True):
            command = [sys.executable] + (["-O"] if optimized else []) + [str(CHECKER)]
            run = subprocess.run(command, input=json.dumps(case["packet"]),
                                 text=True, capture_output=True, timeout=15)
            wanted = "ACCEPT\n" if case["accept"] else "REJECT\n"
            passed = run.stdout == wanted and run.returncode == (0 if case["accept"] else 1)
            if not passed:
                raise RuntimeError("Public CLI mismatch: " + case["name"])
            results.append({"case": case["name"], "optimized": optimized,
                            "expected_accept": case["accept"], "passed": passed})
    receipt = {"cases": len(cases),
               "positive_cases": sum(case["accept"] for case in cases),
               "negative_cases": sum(not case["accept"] for case in cases),
               "in_process_checks": len(cases), "public_cli_checks": len(results),
               "failures": 0, "results": results,
               "scope": "Finite regression tests, not a proof of general soundness."}
    (ROOT / "tests" / "checker_results.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({key: value for key, value in receipt.items() if key != "results"}, indent=2))


if __name__ == "__main__":
    main()
