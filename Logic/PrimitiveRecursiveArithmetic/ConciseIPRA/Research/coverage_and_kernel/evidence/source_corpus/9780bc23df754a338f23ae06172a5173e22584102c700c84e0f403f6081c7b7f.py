"""Replay the complete incidental checkers using only relative package paths.

Run with ordinary Python 3. The checkers themselves are also tested under -O.
The verifier is untrusted evidence and is never imported by any checker.
"""
from pathlib import Path
import ast
import hashlib
import json
import platform
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
VARIANTS = ("import_json.py", "exact_class.py", "exact_type.py", "zero_product.py",
            "ast_not_in.py")
PROGRAMS = ("reference/baseline.py", "reference/baseline_ast.py") + VARIANTS
EXPECTED_METRICS = {
    "reference/baseline.py": (281, 318, 685),
    "reference/baseline_ast.py": (283, 315, 710),
    "import_json.py": (281, 320, 680),
    "exact_class.py": (280, 321, 680),
    "exact_type.py": (281, 322, 676),
    "zero_product.py": (281, 322, 672),
    "ast_not_in.py": (283, 314, 751),
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(path, payload, optimized=False):
    command = [sys.executable] + (["-O"] if optimized else []) + [str(path)]
    result = subprocess.run(command, input=payload, text=True, capture_output=True, timeout=20)
    accepted = result.returncode == 0 and result.stdout.strip() == "ACCEPT"
    protocol = accepted or (result.returncode != 0 and result.stdout.strip() == "REJECT")
    return {"accepted": accepted, "protocol_valid": protocol,
            "exit_code": result.returncode, "stdout": result.stdout.strip()}


def check_transformations():
    principal = (ROOT / "reference/baseline.py").read_text()
    imported = principal.replace("from json import load", "import json").replace(
        "q = load(open(0))", "q = json.load(open(0))")
    assert (ROOT / "import_json.py").read_text() == imported
    predicates = {"exact_class.py": "a.__class__ is list",
                  "exact_type.py": "type(a) is list",
                  "zero_product.py": "a * 0 == []"}
    for name, predicate in predicates.items():
        assert (ROOT / name).read_text() == imported.replace("isinstance(a, list)", predicate)

    old_tree = ast.parse((ROOT / "reference/baseline_ast.py").read_text())
    function = next(n for n in old_tree.body if isinstance(n, ast.FunctionDef) and n.name == "c")
    assert isinstance(function.body[0], ast.Global)
    guard = function.body[1]
    assert isinstance(guard, ast.If) and isinstance(guard.test.ops[0], ast.In)
    assert len(guard.body) == 1 and isinstance(guard.body[0], ast.Return)
    assert not guard.orelse
    guard.test.ops = [ast.NotIn()]
    guard.body = function.body[2:]
    function.body = function.body[:1] + [guard]
    actual = ast.parse((ROOT / "ast_not_in.py").read_text())
    assert ast.dump(old_tree, include_attributes=False) == ast.dump(actual, include_attributes=False)


def measure_programs():
    # In the complete report archive, use ../reference/source_measure.py.
    # The local identical copy keeps this ancillary folder portable by itself.
    measure_path = ROOT.parent / "reference/source_measure.py"
    if not measure_path.is_file():
        measure_path = ROOT / "reference/source_measure.py"
    assert sha(measure_path) == sha(ROOT / "reference/source_measure.py"), "Normalizer mismatch"
    namespace = {"__name__": "inherited_source_measure", "__file__": str(measure_path)}
    exec(compile(measure_path.read_text(), str(measure_path), "exec"), namespace)
    rows = []
    keys = ("normalized_tokens", "ast_nodes", "normalized_bytes")
    for name in PROGRAMS:
        row = {"file": name, **namespace["metrics"](ROOT / name)}
        row["matches_recorded_3_12_profile"] = tuple(row[k] for k in keys) == EXPECTED_METRICS[name]
        rows.append(row)
    report = {
        "python": platform.python_version(), "implementation": platform.python_implementation(),
        "metric": "Entire module, unchanged inherited source_measure.py",
        "normalizer_sha256": sha(measure_path),
        "reference_corpus_envelope": dict(zip(keys, (281, 315, 685))),
        "new_combined_envelope": {k: min(row[k] for row in rows) for k in keys},
        "single_candidate_strictly_below_all_old_coordinates": any(
            all(row[k] < old for k, old in zip(keys, (281, 315, 685)))
            for row in rows if row["file"] in VARIANTS),
        "programs": rows,
    }
    (ROOT / "metrics.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def opener_boundaries():
    namespaces = {}
    for name in PROGRAMS:
        tree = ast.parse((ROOT / name).read_text())
        tree.body = [n for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom,
                                                          ast.Assign, ast.FunctionDef))]
        env = {}
        exec(compile(tree, name, "exec"), env)
        namespaces[name] = env
    values = [[], [0], [0, 0, 0, 0], 0, 1, -1, True, False, 1.5,
              float("nan"), float("inf"), float("-inf"), "", "abc",
              {}, {"__class__": "list"}, None, [{}], [[None]]]
    situations = [(0, None, 0), (1, 0, 0), (3, [-1], -2)]
    records = []
    for number, value in enumerate(values):
        for depth, image, floor in situations:
            outputs = {}
            for name, env in namespaces.items():
                env["k"] = floor
                try:
                    result = env["i"](value, image, depth)
                    outputs[name] = ("value", json.dumps(result, sort_keys=True))
                except Exception:
                    outputs[name] = ("reject",)
            expected = outputs["reference/baseline.py"]
            assert all(result == expected for result in outputs.values()), (number, depth, outputs)
            records.append({"input_index": number, "depth": depth, "floor": floor,
                            "result": expected, "passed": True})
    (ROOT / "opener_validation.json").write_text(json.dumps(
        {"scope": "Finite JSON-type and scope boundary cases; not a universal soundness proof.",
         "case_count": len(records), "programs": list(PROGRAMS), "records": records}, indent=2) + "\n")
    return records


def main():
    provenance = json.loads((ROOT / "PROVENANCE.json").read_text())
    for entry in provenance["files"]:
        path = ROOT / entry["file"]
        assert path.is_file() and sha(path) == entry["sha256"], "Changed inherited payload: " + entry["file"]
    check_transformations()
    measurements = measure_programs()
    cases = json.loads((ROOT / "witness_cases.json").read_text())["cases"]
    inputs = [(c["name"], json.dumps(c["packet"]), c["accept"]) for c in cases]
    inputs += [(c["name"], c["payload"], c["accept"])
               for c in json.loads((ROOT / "malformed_inputs.json").read_text())["cases"]]
    assert len(inputs) == 31
    records = []
    for optimized in (False, True):
        for name, payload, expected in inputs:
            outputs = {program: run(ROOT / program, payload, optimized) for program in PROGRAMS}
            for program, output in outputs.items():
                assert output["protocol_valid"] and output["accepted"] == expected, (
                    program, name, optimized, output)
                assert output["exit_code"] == outputs["reference/baseline.py"]["exit_code"]
            records.append({"case": name, "optimized": optimized, "expected": expected,
                            "outputs": outputs, "passed": True})

    fixtures = {c["name"]: c for c in cases}
    axiom = [0, 0, 0]
    fake_major = [0, [0]]
    bad_major = [[0, axiom, 0, 0], [fake_major, 0, [0], [axiom, 1]], [axiom, [0]]]
    mutation_records = []
    with tempfile.TemporaryDirectory(prefix="mutation_", dir=ROOT) as tmp:
        for name in VARIANTS:
            source = (ROOT / name).read_text()
            proof_lines = [line for line in source.splitlines(keepends=True)
                           if line.strip() == "c(m, g)"]
            assert len(proof_lines) == 1
            changes = [
                ("eager_predecessor", "i([*n, t, u], d=1)", "[*n, t, u]",
                 fixtures["two_child_counter_constant_update"]["packet"]),
                ("major_proof", proof_lines[0], "", bad_major),
                ("equation_only_progress", "len(a) % 2 == m", "m == 0",
                 fixtures["forbidden_compound_progress"]["packet"]),
            ]
            for guard, old, replacement, packet in changes:
                assert source.count(old) == 1
                path = Path(tmp) / name
                path.write_text(source.replace(old, replacement))
                original = run(ROOT / name, json.dumps(packet))
                mutant = run(path, json.dumps(packet))
                assert original["protocol_valid"] and not original["accepted"]
                assert mutant["protocol_valid"] and mutant["accepted"]
                mutation_records.append({"program": name, "guard": guard,
                                         "original_accepts": False, "mutant_accepts": True,
                                         "passed": True})

    opener = opener_boundaries()
    receipt = {
        "status": "PASS", "python": platform.python_version(),
        "scope": "Incidental source variants of the unchanged inherited theory; finite checks and elementary equivalence arguments.",
        "program_hashes": {name: sha(ROOT / name) for name in PROGRAMS},
        "witness_cases_sha256": sha(ROOT / "witness_cases.json"),
        "cases_per_runtime": len(inputs), "runs_per_program": len(records),
        "total_cli_runs": len(records) * len(PROGRAMS),
        "candidate_cli_runs": len(records) * len(VARIANTS),
        "mutation_controls": mutation_records, "opener_boundary_cases": len(opener),
        "metric_profiles_match_recorded": all(r["matches_recorded_3_12_profile"]
                                              for r in measurements["programs"]),
        "results": records,
    }
    (ROOT / "validation.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k not in
                     ("results", "program_hashes", "mutation_controls")}, indent=2))


if __name__ == "__main__":
    main()
