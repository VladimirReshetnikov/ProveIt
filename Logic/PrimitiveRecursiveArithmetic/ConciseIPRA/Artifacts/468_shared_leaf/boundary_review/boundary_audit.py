"""Targeted adversarial review of the 468-byte shifted shared-leaf checker.

Usage: python3 boundary_audit.py PATH/TO/checker468.py [OUTPUT_DIRECTORY]
The two deliberately unsound controls are created only in a temporary directory.
This script is not imported by the measured checker.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import tempfile


def attacks():
    equation = [[7, 0, 0], [7, 0, [0]]]
    goal = [equation]
    closure = [goal, goal, goal]
    numerical_equality = [closure, goal]
    parity = [
        [0, 0, 0, 0],
        [0, 0, 0, 0],
        [0, 0, 0, 0],
        [0, 0, [], 0],
        [[goal], 0, 0, 0],
        [0, equation, goal, goal],
        [numerical_equality, closure, goal, 2],
        [goal, 0],
    ]

    orbit = [[-1], 0, [-1]]
    zero_iterator = [0, orbit, 0]
    major = [zero_iterator, orbit]
    template = [5, orbit]
    goal = [[[7, 0, 9], [7, 0, 7]]]
    computation = [0, 0, orbit, 0]
    early_floor = [
        computation,
        computation,
        [major, zero_iterator, orbit, template],
        [0, 0, 0, 0],
        [0, 0, 0, [-1]],
        [goal, 0],
    ]
    return [
        ("parity", parity, "d % 2 * i(t, d=5)", "i(t, d=5)"),
        ("early_floor", early_floor, "k <= a < d", "k - 1 <= a < d"),
    ]


def main():
    candidate = Path(sys.argv[1]).resolve()
    output = Path(sys.argv[2]) if len(sys.argv) > 2 else Path("boundary_evidence")
    output.mkdir(parents=True, exist_ok=True)
    source = candidate.read_text()
    rows = []
    cases = []
    with tempfile.TemporaryDirectory(prefix="ipra-boundary-") as temporary:
        for name, data, before, after in attacks():
            if source.count(before) != 1:
                raise ValueError((name, "Unexpected candidate source"))
            mutant = Path(temporary) / ("UNSOUND_" + name + ".py")
            mutant.write_text(source.replace(before, after))
            payload = (json.dumps(data, separators=(",", ":")) + "\n").encode()
            filename = "false_" + name + "_goal.json"
            (output / filename).write_bytes(payload)
            cases.append({"name": name, "file": filename, "packets": len(data) - 1,
                          "sha256": hashlib.sha256(payload).hexdigest(),
                          "mutation": {"from": before, "to": after}})
            for program, label, expected in [(candidate, "candidate", False),
                                              (mutant, "unsound_control", True)]:
                for optimized in [False, True]:
                    command = [sys.executable, "-I", "-S", "-B"]
                    if optimized:
                        command.append("-O")
                    command.append(str(program))
                    result = subprocess.run(command, input=payload, capture_output=True,
                                            timeout=10)
                    accepted = result.returncode == 0 and result.stdout == b"ACCEPT\n"
                    rows.append({"case": name, "program": label,
                                 "optimized": optimized, "expected": expected,
                                 "accepted": accepted, "passed": accepted == expected})
    report = {"python": sys.version, "candidate_file": candidate.name,
              "candidate_sha256": hashlib.sha256(candidate.read_bytes()).hexdigest(),
              "cases": cases, "executions": len(rows),
              "failures": [row for row in rows if not row["passed"]], "results": rows}
    (output / "boundary_review.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items() if key != "results"}, indent=2))
    if report["failures"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
