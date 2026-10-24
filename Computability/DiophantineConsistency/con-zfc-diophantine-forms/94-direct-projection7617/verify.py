#!/usr/bin/env python3
"""Verify, rebuild and adversarially check the frozen direct quartic release.

Uses Python's standard library. Work is performed in a fresh temporary copy.
The original package is read-only, apart from an explicitly requested receipt.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile

CORE = ["circuit_integer.json", "residuals_integer.json", "equation_integer.json",
        "summary_integer.json", "row_source.json", "source_circuit_before_pruning.json"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--optimized", action="store_true")
    parser.add_argument("--skip-mutations", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    stages = []
    python = [sys.executable] + (["-O"] if args.optimized else [])

    manifest_path = root / "MANIFEST.json"
    if manifest_path.exists():
        manifest = json.loads(manifest_path.read_text())
        for item in manifest["files"]:
            file = root / item["path"]
            if not file.is_file() or sha(file) != item["sha256"]:
                raise ValueError("Release manifest mismatch: " + item["path"])

    with tempfile.TemporaryDirectory(prefix="con-zfc-direct-verify-") as tmp:
        copy = Path(tmp) / "package"
        shutil.copytree(root, copy, ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        rebuilt = Path(tmp) / "rebuilt"

        def run(label, command, reject=False):
            result = subprocess.run(python + command, cwd=copy, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            passed = result.returncode != 0 if reject else result.returncode == 0
            stages.append({"stage": label, "exit_code": result.returncode,
                           "expected_rejection": reject, "passed": passed,
                           "stdout_sha256": hashlib.sha256(result.stdout.encode()).hexdigest()})
            if not passed:
                raise RuntimeError(label + " failed\n" + result.stdout[-6000:])

        run("source_projection", ["source/check_projection.py"])
        run("fresh_build", ["build.py", "--output", str(rebuilt)])
        byte_matches = {}
        for name in CORE:
            byte_matches[name] = (root / "equations" / name).read_bytes() == (rebuilt / name).read_bytes()
            if not byte_matches[name]:
                raise ValueError("Nonidentical rebuild: " + name)
        run("independent_expansion", ["check_exact.py", str(rebuilt)])
        run("independent_semantics", ["check_signed_independent.py", str(rebuilt),
                                      "--natural-source", "source/circuit.json"])

        if not args.skip_mutations:
            # An altered expanded coefficient must be rejected even though the
            # variable count, domain, and degree remain plausible.
            p = rebuilt / "equation_integer.json"
            original = p.read_bytes()
            data = json.loads(original)
            data["terms"][0][0] += 1
            p.write_text(json.dumps(data, separators=(",", ":")) + "\n")
            run("reject_changed_polynomial_coefficient", ["check_exact.py", str(rebuilt)], True)
            p.write_bytes(original)

            # Removing a necessary semantic domain guard must not pass merely
            # because the remaining graph is structurally well-formed.
            p = rebuilt / "residuals_integer.json"
            original = p.read_bytes()
            rows = json.loads(original)
            if not rows[-1]["label"].startswith("semantic nonnegativity "):
                raise ValueError("Unexpected final guard position")
            rows.pop()
            p.write_text(json.dumps(rows, separators=(",", ":")) + "\n")
            run("reject_missing_natural_guard", ["check_exact.py", str(rebuilt)], True)
            p.write_bytes(original)

            # Confusing a rule-parameter bound with the quotient bound would
            # invalidate the proof-height theorem. Check that it is detected.
            p = copy / "source" / "circuit.json"
            original = p.read_bytes()
            source = json.loads(original)
            binding = source["source_binding"]
            binding["coordinate_bounds"][0] = binding["U"]
            p.write_text(json.dumps(source, separators=(",", ":")) + "\n")
            run("reject_wrong_coordinate_bound", ["source/check_projection.py"], True)
            p.write_bytes(original)

    summary = json.loads((root / "equations" / "summary_integer.json").read_text())
    result = {"status": "PASS", "python": platform.python_version(),
              "optimized": args.optimized, "core_byte_matches": byte_matches,
              "stages": stages, "metrics": summary,
              "polynomial_sha256": sha(root / "equations" / "equation_integer.json"),
              "scope": "Exact finite source bindings, arithmetic interfaces, graph reconstruction, polynomial expansion and rebuild. The unbounded proofs and inherited logical/Pell theorems are separate mathematical inputs."}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
