"""Check the complete AST profile, including the newly decoded iterable aliases."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


def main():
    checker = ROOT / "code/checker_ast.py"
    cases = json.loads((ROOT / "tests/ast_profile_cases.json").read_text())
    records = []
    for optimized in (False, True):
        for case in cases["cases"]:
            command = [sys.executable] + (["-O"] if optimized else []) + [str(checker)]
            run = subprocess.run(command, input=json.dumps(case["packet"]),
                                 text=True, capture_output=True, timeout=10)
            accepted = run.returncode == 0 and run.stdout.strip() == "ACCEPT"
            rejected = run.returncode != 0 and run.stdout.strip() == "REJECT"
            records.append({"name": case["name"], "optimized": optimized,
                            "expected_accept": case["accept"],
                            "accepted": accepted, "exit_status": run.returncode,
                            "passed": accepted if case["accept"] else rejected})
    result = {"scope": "Finite complete-process checks, not a formal metatheory",
              "checker_sha256": hashlib.sha256(checker.read_bytes()).hexdigest(),
              "canonical_case_count": cases["canonical_case_count"],
              "alias_case_count": cases["alias_case_count"],
              "cli_runs": len(records), "passed_runs": sum(r["passed"] for r in records),
              "failures": [r for r in records if not r["passed"]], "results": records}
    (ROOT / "evidence/ast_profile_validation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key != "results"}, indent=2))
    if result["failures"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
