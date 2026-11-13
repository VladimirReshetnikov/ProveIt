"""Regression and phase-boundary checks for native600 and strict625.

All fixtures and controls are local. Candidate proof checkers are standalone.
"""
import concurrent.futures
import copy
import json
from pathlib import Path
import subprocess
import sys

from compile_native import convert
from native_mode_regression import regression

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "fixtures/validated"


def run(job):
    label, kind, program, data, expected = job
    results = []
    for optimized in (False, True):
        command = [sys.executable, "-I", "-S", "-B"]
        if optimized:
            command.append("-O")
        command.append(str(ROOT / program))
        p = subprocess.run(command, input=data, capture_output=True, timeout=20)
        accepted = p.returncode == 0 and p.stdout == b"ACCEPT\n"
        results.append({"optimized": optimized, "accepted": accepted,
                        "passed": accepted == expected})
    return {"fixture": label, "kind": kind, "program": program,
            "expected": expected, "results": results}


def encode(value):
    return json.dumps(value, separators=(",", ":")).encode()


def main():
    jobs, conversions = [], []
    for group in ("native", "strict_proofs", "strict_boundary"):
        candidate = "code/checker_native.py" if group == "native" else "code/checker_strict.py"
        control = "controls/native596.py" if group == "native" else "controls/strict621.py"
        directory = FIXTURES / group
        for case in json.loads((directory / "cases.json").read_text()):
            name, expected = case["file"], case["expected"]
            raw = (directory / "source" / name).read_bytes()
            label = group + "/" + name
            jobs.append((label, "upstream-control", control, raw, expected))
            if expected:
                converted, statistics = convert(json.loads(raw))
                saved = json.loads((directory / "leaves" / name).read_text())
                if converted != saved or converted[-1] != json.loads(raw)[-1]:
                    raise ValueError("conversion did not reproduce with the same goal: " + label)
                conversions.append({"fixture": label, "statistics": statistics})
                jobs.append((label, "translated-positive", candidate, encode(saved), True))
                bad = copy.deepcopy(saved)
                bad[-1] = [0, [0]]
                jobs.append((label, "false-goal", candidate, encode(bad), False))
            else:
                jobs.append((label, "inherited-negative", candidate, raw, False))

    # Exercise the whole-input lexical guard with an otherwise accepted proof.
    valid = json.loads((FIXTURES / "strict_proofs/leaves/computation_zero_local.json").read_text())
    for index, malformed in enumerate((True, False, 0.0, 1.25, None, "x", {}, {"x": 0})):
        modified = [malformed] + copy.deepcopy(valid)
        for candidate, expected in (("code/checker_native.py", True), ("code/checker_strict.py", False)):
            jobs.append(("unused_prefix_" + str(index), "alphabet-boundary",
                         candidate, encode(modified), expected))
    # The new leaf allows the literal-zero seed directly, a genuine axiom.
    direct = [[0, 0, 0, 0], [[0, 0, 0], 0]]
    for candidate in ("code/checker_native.py", "code/checker_strict.py"):
        jobs.append(("literal_zero_seed", "direct-axiom", candidate, encode(direct), True))

    # Removing the old truthy-seed computation branch requires this added guard:
    # progress is allowed only for an equation matrix AND the zero mode flag.
    # Otherwise u=1 would accidentally select induction on a compound matrix.
    selector_cases = []
    for matrix_arity in (1, 2, 3):
        for flag in (0, [], 1, [0], -1, 2):
            selected = matrix_arity % 2 == flag == 0
            intended = matrix_arity == 2 and flag == 0
            selector_cases.append({"matrix_arity": matrix_arity, "flag": flag,
                                   "progress": selected, "passed": selected == intended})
    if not all(case["passed"] for case in selector_cases):
        raise ValueError("the native progress restriction failed")
    mode_regression = regression(ROOT / "code/checker_strict.py")

    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run, jobs))
    failures = [r for r in results if any(not x["passed"] for x in r["results"])]
    report = {"python": sys.version, "executions": 2 * len(results),
              "converted_cases": len(conversions), "failures": failures,
              "native_progress_guard": selector_cases,
              "actual_checker_mode_regression": mode_regression,
              "conversions": conversions, "results": results}
    (ROOT / "evidence/validated_reproduction.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("executions", "converted_cases", "failures")}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
