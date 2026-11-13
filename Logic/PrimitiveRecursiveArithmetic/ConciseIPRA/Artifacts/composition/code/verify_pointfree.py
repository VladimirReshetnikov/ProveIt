"""Exercise the standalone checker in normal and optimized Python."""
import json
import subprocess
import sys
from pathlib import Path


def main():
    root = Path(__file__).resolve().parent.parent
    checker = root / "code" / "pointfree_checker.py"
    rows = []
    for path in sorted((root / "examples").glob("*.json")):
        expected = not path.name.startswith("reject_")
        for optimized in (False, True):
            command = [sys.executable] + (["-O"] if optimized else []) + [str(checker)]
            result = subprocess.run(command, input=path.read_bytes(), capture_output=True,
                                    timeout=10)
            accepted = result.returncode == 0 and result.stdout == b"ACCEPT\n"
            rows.append(dict(example=path.name, optimized=optimized,
                             expected=expected, accepted=accepted,
                             exit_code=result.returncode))
            if accepted != expected:
                raise RuntimeError((path.name, optimized, result.stderr.decode()))
    positive = json.loads((root / "examples" / "all_rules.json").read_text())
    tags = sorted({node[0] for node in positive})
    expected_tags = {"C0", "CL", "CR", "CE", "P00", "P0S", "PS", "J0", "JS",
                     "Hyp", "Sub", "Post", "Pair", "Transport", "QE", "DE", "DI", "QI", "Ind"}
    if set(tags) != expected_tags:
        raise RuntimeError("primitive rule coverage differs")
    receipt = dict(status="passed", executions=len(rows), primitive_schemas=tags,
                   proof_nodes=len(positive), results=rows,
                   scope="implementation checks; no claim of machine-verified metatheory")
    (root / "evidence").mkdir(exist_ok=True)
    (root / "evidence" / "pointfree_checks.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k != "results"}))


if __name__ == "__main__":
    main()
