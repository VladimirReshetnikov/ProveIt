"""Remeasure complete sources and replay the focused public checker interface.

This is supporting evidence, not a formal proof of universal correctness.
"""
import ast
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    measure = module("source_measure", ROOT / "reference/source_measure.py")
    producers = module("make_fixtures", ROOT / "code/make_fixtures.py")
    manifest = json.loads((ROOT / "reference/provenance.json").read_text())
    for entry in manifest["files"]:
        path = ROOT / entry["local_file"]
        require(hashlib.sha256(path.read_bytes()).hexdigest() == entry["sha256"],
                "Changed frozen comparator: " + entry["local_file"])
    source_paths = ["reference/minimum_tokens.py", "reference/minimum_ast.py",
                    "reference/minimum_bytes.py", "reference/choice_deferred_tokens.py",
                    "code/all_starts_checker.py"]
    measurements = [{"file": path, **measure.metrics(ROOT / path)}
                    for path in source_paths]
    (ROOT / "evidence/measurements.json").write_text(
        json.dumps({"python": platform.python_version(), "programs": measurements},
                   indent=2) + "\n")

    records = json.loads((ROOT / "evidence/focused_certificates.json").read_text())["cases"]
    results = []
    for optimized in (False, True):
        command = [sys.executable] + (["-O"] if optimized else []) + [
            str(ROOT / "code/all_starts_checker.py")]
        for case in records:
            run = subprocess.run(command, input=json.dumps(case["packet"]),
                                 text=True, capture_output=True, timeout=10)
            expected = ("ACCEPT\n", 0) if case["accept"] else ("REJECT\n", 1)
            actual = run.stdout, run.returncode
            require(actual == expected and run.stderr == "",
                    "Public verdict mismatch: " + case["name"])
            results.append({"name": case["name"], "optimized": optimized,
                            "accepted": case["accept"], "exit_code": run.returncode})
        for label, raw in (("invalid_json", "["), ("not_packet_array", "{}"),
                           ("empty_packet", "[]")):
            run = subprocess.run(command, input=raw, text=True, capture_output=True, timeout=10)
            require((run.stdout, run.returncode, run.stderr) == ("REJECT\n", 1, ""),
                    "Malformed public input did not reject: " + label)
            results.append({"name": label, "optimized": optimized,
                            "accepted": False, "exit_code": run.returncode})

    source = (ROOT / "code/all_starts_checker.py").read_text()
    mutants = {
        "skip_endpoint_root_validation": ("s, u = i(u)", "s, u = u",
                                           "exposed_endpoint_1_1"),
        "grant_compound_induction": ("k if m or len(a) % 2 == 0 else 0", "k",
                                      "forbidden_compound_induction"),
        "allow_failed_major_fallback": ("if m:\n        1 / c(m, g)",
                                         "if m and c(m, g):",
                                         "failed_major_cannot_fall_through"),
    }
    controls = []
    for name, (old, new, probe) in mutants.items():
        require(source.count(old) == 1, "Mutation target changed: " + name)
        tree = ast.parse(source.replace(old, new))
        tree.body.pop()
        ns = {}
        exec(compile(tree, "<controlled mutant>", "exec"), ns)
        case = next(row for row in records if row["name"] == probe)
        actual = producers.run_core(case["packet"], namespace=ns)[0]
        require(not case["accept"] and actual, "Guard probe did not exercise " + name)
        controls.append({"mutant": name, "probe": probe,
                         "original_accepts": False, "mutant_accepts": True})

    receipt = {"python": platform.python_version(),
               "checker_sha256": hashlib.sha256(source.encode()).hexdigest(),
               "focused_cases": len(records),
               "positive_cases": sum(row["accept"] for row in records),
               "negative_cases": sum(not row["accept"] for row in records),
               "public_cli_runs": len(results), "all_passed": True,
               "runs": results, "guard_controls": controls,
               "scope": "Finite certificate and boundary checks, not a proof-assistant formalization."}
    (ROOT / "evidence/validation.json").write_text(json.dumps(receipt, indent=2) + "\n")
    (ROOT / "evidence/guard_controls.json").write_text(json.dumps(controls, indent=2) + "\n")
    print(json.dumps({"public_cli_runs": len(results), "all_passed": True,
                      "guard_controls": len(controls),
                      "measurements": [{"file": row["file"],
                                        "tokens": row["normalized_tokens"],
                                        "ast": row["ast_nodes"],
                                        "bytes": row["normalized_bytes"]}
                                       for row in measurements]}, indent=2))


if __name__ == "__main__":
    main()
