#!/usr/bin/env python3
"""Run every finite check without changing recorded evidence. New code: MIT-0."""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent


def normalized(value):
    if isinstance(value, dict):
        return {k: normalized(v) for k, v in value.items()
                if k not in {"seconds", "elapsed_seconds"}}
    if isinstance(value, list):
        return [normalized(v) for v in value]
    return value


def main():
    output = ROOT / "reproduced"
    output.mkdir(exist_ok=True)
    records = []
    with tempfile.TemporaryDirectory(prefix="zfc-cyclic-repro-") as temporary:
        stage = Path(temporary)
        shutil.copytree(ROOT / "code", stage / "code",
                        ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        (stage / "examples").mkdir()
        (stage / "data").mkdir()
        code = stage / "code"
        env = dict(os.environ)
        env["PYTHONPATH"] = str(code)
        env["PYTHONDONTWRITEBYTECODE"] = "1"

        def run(name, script, args, generated, stdout_json=False):
            command = [sys.executable, str(code / script), *map(str, args)]
            result = subprocess.run(command, cwd=stage, env=env,
                                    text=True, capture_output=True)
            if result.returncode:
                raise RuntimeError(f"{name} failed:\n{result.stdout[-3000:]}\n"
                                   f"{result.stderr[-3000:]}")
            value = json.loads(result.stdout) if stdout_json else json.loads(
                Path(generated).read_text())
            expected = ROOT / "data" / name
            if not expected.exists():
                raise RuntimeError(f"Missing reference snapshot: {expected}")
            if normalized(value) != normalized(json.loads(expected.read_text())):
                destination = output / name
                destination.write_text(json.dumps(value, indent=2) + "\n")
                raise RuntimeError(f"Deterministic result differs: {name}; fresh result saved")
            (output / name).write_text(json.dumps(value, indent=2) + "\n")
            records.append({"result": name, "status": "PASS",
                            "matches_reference_ignoring_elapsed_time": True})
            print(f"PASS {name}", flush=True)

        run("rotation9_evidence.json", "test_rotation9.py", [],
            code / "rotation9_evidence.json")
        run("cyclic_audit_results.json", "cyclic_audit.py", [],
            code / "cyclic_audit_results.json")
        run("finite_source_review_results.json", "review_nbg14.py", [],
            None, stdout_json=True)
        run("finite_nbg14.json", "finite_nbg.py", [stage / "source.json"],
            stage / "source.json")
        run("finite_nbg14_packed.json", "graph_wrapper.py",
            [stage / "source.json", stage / "packed.json"], stage / "packed.json")
        run("graph_wrapper_results.json", "test_graph_wrapper.py",
            [stage / "graph.json"], stage / "graph.json")
        run("phase_optimizer_results.json", "test_phase_optimizer.py",
            ["--reference", code / "rotation9.py", "--output", stage / "phase9.json"],
            stage / "phase9.json")
        run("phase_optimizer8_results.json", "test_phase_optimizer8.py",
            ["--output", stage / "phase8.json"], stage / "phase8.json")
        run("public_baseline_audit.json", "audit_public_baselines.py",
            ["--machine254", ROOT / "benchmarks/zfc_254.tm",
             "--machine253", ROOT / "benchmarks/zfc_253.tm",
             "--output", stage / "baseline.json"], stage / "baseline.json")

    summary = {"status": "PASS", "python": sys.version.split()[0],
               "checks": records,
               "scope": "finite execution and deterministic artifact reproduction only",
               "new_kernel_rebuild": False, "new_binary_machine": False}
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print("All finite suites passed. No new kernel or binary-machine claim.")


if __name__ == "__main__":
    main()
