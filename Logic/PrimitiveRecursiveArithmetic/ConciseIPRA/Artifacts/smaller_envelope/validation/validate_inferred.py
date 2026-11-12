"""Finite process-level checks and accepting-trace repair demonstrations.

This is untrusted validation support. No checker imports this module.
It uses each profile's own scope convention and does not rename parameters.
"""
from __future__ import annotations

import argparse
import ast
import copy
import hashlib
import json
import platform
import subprocess
import sys
from collections import Counter
from pathlib import Path


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")


def run(checker, data, optimized):
    command = [sys.executable] + (["-O"] if optimized else []) + [str(checker)]
    try:
        result = subprocess.run(command, input=json.dumps(data).encode(),
                                capture_output=True, timeout=15)
    except subprocess.TimeoutExpired:
        return {"accepted": False, "outcome": "timeout"}
    accepted = result.returncode == 0 and result.stdout == b"ACCEPT\n"
    return {"accepted": accepted, "returncode": result.returncode,
            "outcome": "ACCEPT" if accepted else "reject",
            "stderr_tail": result.stderr.decode(errors="replace").splitlines()[-1:]}


def trace(checker, data, profile):
    """Instrument the candidate's actual functions, retaining their logic.

    The instrumentation observes consumed packets immediately before the
    recursive major check. It does not implement an alternative calculus.
    Only top-level input/output is removed. The inferred checker itself is
    still tested in a separate process for every case.
    """
    source = checker.read_text()
    pop_line = "        m, s, u, t = q()\n"
    infer_line = "            m = [s, u] if s else [t] * 3\n"
    major_line = "        h = "
    if source.count(pop_line) != 1 or source.count(infer_line) != 1:
        raise ValueError("Unrecognized candidate instrument points")
    source = source.replace(pop_line, pop_line + "        _start(a, k)\n")
    source = source.replace(infer_line, infer_line + "            _inferred()\n")
    source = source.replace(major_line, "        _record(m, a, k)\n" + major_line)
    tree = ast.parse(source)
    tree.body = [node for node in tree.body if
                 isinstance(node, (ast.Import, ast.ImportFrom, ast.FunctionDef))
                 or isinstance(node, ast.Assign) and len(node.targets) == 1
                 and isinstance(node.targets[0], ast.Name)
                 and node.targets[0].id == "k"]
    stream = copy.deepcopy(data)
    goal = stream.pop()
    records = []
    current = None

    def pop():
        nonlocal current
        index = len(stream) - 1
        packet = stream.pop()
        current = {"index": index, "supplied_major": copy.deepcopy(packet[0]),
                   "inferred": False}
        records.append(current)
        return packet

    def start(a, k):
        current["goal_before"] = copy.deepcopy(a)
        current["floor_before"] = k

    def inferred():
        current["inferred"] = True

    def record(m, a, k):
        current["actual_major"] = copy.deepcopy(m)
        current["goal_after"] = copy.deepcopy(a)
        current["floor_at_major"] = k

    namespace = {"q": pop, "_start": start, "_inferred": inferred,
                 "_record": record}
    exec(compile(tree, str(checker) + ":instrumented", "exec"), namespace)
    if profile == "global":
        namespace["c"](goal, ())
    else:
        namespace["c"](goal)
    repaired = copy.deepcopy(data)
    for event in records:
        repaired[event["index"]][0] = event["actual_major"]
    return repaired, records


def validate(root, output):
    candidates = {
        "local": root / "checkers/ast.py",
        "global": root / "checkers/tokens.py",
    }
    controls = {
        "local": root / "reference/checkers/ast.py",
        "global": root / "reference/checkers/tokens.py",
    }
    output.mkdir(parents=True, exist_ok=True)
    cases = []
    manifest = json.loads((root / "fixtures/manifest.json").read_text())
    for item in manifest["cases"]:
        path = root / item["path"]
        if hashlib.sha256(path.read_bytes()).hexdigest() != item["sha256"]:
            raise ValueError("Frozen fixture changed: " + item["path"])
        cases.append({**item, "data": json.loads(path.read_text())})

    receipts = []
    mismatches = []
    repair_records = []

    def compare(case, checker, role, data=None, expectation=None):
        data = case["data"] if data is None else data
        expectation = case["expected"] if expectation is None else expectation
        for optimized in (False, True):
            result = run(checker, data, optimized)
            item = {"case": case["name"], "group": case["group"],
                    "profile": case["profile"], "role": role,
                    "optimized": optimized, "expected": expectation, **result}
            receipts.append(item)
            if result["accepted"] != expectation or result["outcome"] == "timeout":
                mismatches.append(item)

    for case in cases:
        profile = case["profile"]
        compare(case, controls[profile], "control")
        compare(case, candidates[profile], "candidate")

    # Only canonical-profile positive certificates are edited. Copying exact
    # global/local variants avoids any unsound heuristic eigenname conversion.
    generated = []
    for case in cases:
        if not case["expected"]:
            continue
        profile = case["profile"]
        repaired, records = trace(candidates[profile], case["data"], profile)
        inferred_indices = [r["index"] for r in records if r["inferred"]]
        if not inferred_indices:
            continue
        erased = copy.deepcopy(case["data"])
        for index in inferred_indices:
            erased[index][0] = 0
        new_name = "erased_" + case["name"]
        new_case = {"name": new_name, "profile": profile,
                    "group": "erased_inferred_major", "expected": True, "data": erased}
        compare(new_case, candidates[profile], "candidate")
        repaired, erased_records = trace(candidates[profile], erased, profile)
        compare(new_case, controls[profile], "repaired_control", repaired)
        direct_control = run(controls[profile], erased, False)
        repair_records.append({"case": new_name, "profile": profile,
                               "consumed_packets": len(erased_records),
                               "inferred_packets": len(inferred_indices),
                               "erased_control_accepted": direct_control["accepted"],
                               "erased_sha256": hashlib.sha256(json.dumps(erased).encode()).hexdigest(),
                               "repaired_sha256": hashlib.sha256(json.dumps(repaired).encode()).hexdigest()})
        receipts.append({"case": new_name, "group": "erased_contract_comparison",
                         "profile": profile, "role": "unrepaired_control",
                         "optimized": False, "expected": None, **direct_control})
        write_json(root / "fixtures/inferred" / (new_name + ".json"), erased)
        write_json(root / "fixtures/repaired" / (new_name + ".json"), repaired)
        generated.append(new_case)

    for profile in candidates:
        for name, data in [
            ("inferred_false_major_has_no_proof", [[0, 0, [0], [0, 3]], [0, [0]]]),
            ("inferred_source_is_future_parameter", [[0, -1, [0], [3, 0]], [[0], 0]]),
            ("inferred_mismatched_endpoint", [[0, [0], 0, [3, [0]]], [[0], [0]]]),
        ]:
            case = {"name": name + "_" + profile, "profile": profile,
                    "group": "targeted_attack", "expected": False, "data": data}
            compare(case, candidates[profile], "candidate")
            write_json(root / "fixtures/attacks" / (case["name"] + ".json"), data)

        original = next(c for c in generated if c["profile"] == profile
                        and c["name"] == "erased_kernel_transport_reflexivity_" + profile)
        damaged = copy.deepcopy(original["data"])
        # The root is inferred transport; delete its recursive major's sole
        # computation certificate, retaining the same theorem as a goal.
        if len(damaged) != 4:
            raise ValueError("Unexpected reflexivity fixture structure")
        del damaged[1]
        case = {"name": "omitted_inferred_major_proof_" + profile,
                "profile": profile, "group": "targeted_attack",
                "expected": False, "data": damaged}
        compare(case, candidates[profile], "candidate")
        write_json(root / "fixtures/attacks" / (case["name"] + ".json"), damaged)

    counts = Counter((r["group"], r["role"], r["expected"]) for r in receipts)
    summary = {
        "python": platform.python_version(),
        "repository_commit": "62396b06020f794fa6dc01b4025a6a5db9d4d28a",
        "inherited_cases": len(cases),
        "inherited_positive_cases": sum(c["expected"] for c in cases),
        "inherited_negative_cases": sum(not c["expected"] for c in cases),
        "erased_major_certificates": len(generated),
        "erased_major_packets": sum(r["inferred_packets"] for r in repair_records),
        "erased_certificates_rejected_by_old_control":
            sum(not r["erased_control_accepted"] for r in repair_records),
        "targeted_attack_cases": 8,
        "process_executions": len(receipts),
        "expected_acceptances": sum(r["expected"] is True for r in receipts),
        "expected_rejections": sum(r["expected"] is False for r in receipts),
        "unconstrained_contract_comparisons": sum(r["expected"] is None for r in receipts),
        "mismatches": mismatches,
        "counts": [{"group": g, "role": r, "expected": e, "count": n}
                   for (g, r, e), n in counts.items()],
        "source_sha256": {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in list(candidates.values()) + list(controls.values())},
        "limits": [
            "Finite process checks and trace observations, not a formal soundness proof.",
            "Global and local scope fixtures are distinct and are never heuristically renamed.",
            "The extra zero-neutral fixtures run only with the local AST scope profile.",
            "The unguarded-progressive fixture is administrative, not a canonical public formula.",
            "A false goal rejection here is a test of these certificates, not theorem unprovability.",
        ],
    }
    write_json(output / "inferred_validation.json", {**summary, "receipts": receipts})
    write_json(output / "trace_repair_summary.json", repair_records)
    write_json(output / "inferred_summary.json", summary)
    print(json.dumps({k: v for k, v in summary.items()
                      if k not in {"counts", "source_sha256", "limits", "mismatches"}}, indent=2))
    if mismatches:
        print(json.dumps(mismatches, indent=2))
        raise SystemExit(1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path,
                        default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    package_root = args.root.resolve()
    output = args.output.resolve() if args.output else package_root / "evidence"
    validate(package_root, output)
