"""Reproduce the standalone byte-profile conversion and regression checks.

The measured checker imports none of this untrusted test infrastructure.
"""
import concurrent.futures
import json
from pathlib import Path
import subprocess
import sys

from compile_bytes import convert

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "fixtures/bytes"
CONTROL = ROOT / "controls/bytes477.py"
CANDIDATE = ROOT / "code/checker_bytes.py"


def execute(job):
    name, kind, program, data, expected = job
    results = []
    for optimized in (False, True):
        command = [sys.executable, "-I", "-S", "-B"]
        if optimized:
            command.append("-O")
        command.append(str(program))
        process = subprocess.run(command, input=data, capture_output=True, timeout=20)
        accepted = process.returncode == 0 and process.stdout == b"ACCEPT\n"
        results.append({"optimized": optimized, "accepted": accepted,
                        "passed": accepted == expected})
    return {"fixture": name, "kind": kind, "expected": expected,
            "results": results}


def main():
    for program in (CONTROL, CANDIDATE):
        if not program.is_file():
            raise FileNotFoundError(program)
    cases = json.loads((FIXTURES / "cases.json").read_text())
    jobs = []
    conversions = []
    for case in cases:
        name, expected = case["file"], case["expected"]
        data = (FIXTURES / "source" / name).read_bytes()
        jobs.append((name, "upstream-control", CONTROL, data, expected))
        if expected:
            converted, statistics = convert(json.loads(data))
            retained = json.loads((FIXTURES / "leaves" / name).read_text())
            if converted != retained:
                raise ValueError("nonreproducing converted certificate: " + name)
            if converted[-1] != json.loads(data)[-1]:
                raise ValueError("public goal or initial floor changed: " + name)
            conversions.append({"fixture": name, "statistics": statistics})
            encoded = json.dumps(converted, separators=(",", ":")).encode()
            jobs.append((name, "translated-positive", CANDIDATE, encoded, True))
            converted[-1] = [[0, [0]], 0]
            encoded = json.dumps(converted, separators=(",", ":")).encode()
            jobs.append((name, "false-goal", CANDIDATE, encoded, False))
        else:
            jobs.append((name, "inherited-negative", CANDIDATE, data, False))
    jobs.append(("direct_zero_seed.json", "new-direct-axiom", CANDIDATE,
                 (FIXTURES / "direct_zero_seed.json").read_bytes(), True))
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(execute, jobs))
    failures = [r for r in results if any(not x["passed"] for x in r["results"])]
    report = {"python": sys.version, "executions": 2 * len(results),
              "converted_cases": len(conversions), "failures": failures,
              "conversions": conversions, "results": results}
    (ROOT / "evidence/byte_reproduction.json").write_text(
        json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in
                      ("executions", "converted_cases", "failures")}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
