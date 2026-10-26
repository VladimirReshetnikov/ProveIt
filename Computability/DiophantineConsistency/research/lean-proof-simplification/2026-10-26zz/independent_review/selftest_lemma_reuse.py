#!/usr/bin/env python3
"""Replay independent audit in both Python modes and test hash-refusal guards.

Only temporary copies are mutated. No Lean program is invoked.
"""
from pathlib import Path
import ast
import hashlib
import json
import subprocess
import sys
import tempfile


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    root = Path(__file__).resolve().parent.parent
    script = root / "independent_review/check_lemma_reuse.py"
    require(not any(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(Path(__file__).read_text()))),
            "selftest must not rely on Python assert")
    mode_results = []
    for optimized in (False, True):
        result = subprocess.run([sys.executable] + (["-O"] if optimized else []) + [str(script)],
                                capture_output=True, text=True)
        require(result.returncode == 0, f"clean replay failed: {result.stderr}")
        mode_results.append(json.loads(result.stdout))
    mode_results[0].pop("python_optimization_level")
    mode_results[1].pop("python_optimization_level")
    require(mode_results[0] == mode_results[1], "normal/optimized outcomes differ beyond mode")
    targets = [
        ("sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeOuterSeedConstruction.lean", "source sha256 mismatch"),
        ("research/outer_seed/NativeOuterSeedConstruction.lean", "candidate sha256 mismatch"),
        ("dependencies/Computability/HilbertTenthProblem/Lean/Diophantine/Common/PellMod.lean", "helper sha256 mismatch"),
    ]
    rows = []
    for index, (target, expected_error) in enumerate(targets):
        for optimized in (False, True):
            with tempfile.TemporaryDirectory(prefix="round7-independent-negative-") as temporary:
                temp = Path(temporary)
                for previous, _ in targets[:index+1]:
                    destination = temp / previous
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    data = (root / previous).read_bytes()
                    if previous == target:
                        data += b"\n-- deliberate negative-control mutation\n"
                    destination.write_bytes(data)
                result = subprocess.run([sys.executable] + (["-O"] if optimized else []) +
                                        [str(script), "--root", str(temp)], capture_output=True, text=True)
                require(result.returncode == 1 and expected_error in result.stderr,
                        f"negative-control guard failed: {target}, optimization={optimized}, {result}")
                rows.append({"mutated_path": target, "optimized": optimized,
                             "expected_error": expected_error, "exit_code": result.returncode,
                             "stderr": result.stderr.strip(), "status": "REJECTED_AS_EXPECTED"})
    print(json.dumps({
        "status": "PASS",
        "script_sha256": hashlib.sha256(script.read_bytes()).hexdigest(),
        "normal_optimized_equal_except_mode": True,
        "negative_controls": rows,
        "scope": "Source-integrity refusal tests, not Lean validation.",
    }, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, KeyError, ValueError, OSError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
