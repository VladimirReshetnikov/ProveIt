"""Explicit endpoint and scope countercertificates, plus mutation probes."""
import argparse
import ast
import copy
import hashlib
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from replay import run


COMPUTE = [0, 0, 0, 0]
ZERO_BOX = [0, 0, 0]
ONE = [0]


def reflexivity_instructions(term):
    box = [0, term, 0]
    equation = [box, term]
    return [copy.deepcopy(COMPUTE), copy.deepcopy(COMPUTE),
            [equation, box, term, [1, term]]]


def closure_instructions(body, step_is_computation):
    paired = [0, 0, body]
    result = [[0, 0, 0, ZERO_BOX], [paired, 0, 0, 0]]
    if step_is_computation:
        result.insert(0, copy.deepcopy(COMPUTE))
    return result


def make_cases():
    box_zero = [0, 0, 0]
    valid_equation = [box_zero, 0]
    threshold_body = [[5, 0, ONE], ONE]
    threshold_closure = [threshold_body]
    threshold_proof = closure_instructions(threshold_body, True)
    constant_body = [0, 0]
    constant_closure = [constant_body]
    constant_proof = closure_instructions(constant_body, False)
    cases = [
        {"name": "valid_computation", "packet": [COMPUTE, valid_equation], "accept": True},
        {"name": "valid_reflexivity_one", "packet": reflexivity_instructions(ONE) + [[ONE, ONE]], "accept": True},
        {"name": "valid_threshold_closure", "packet": threshold_proof + [threshold_closure], "accept": True},
        {"name": "valid_constant_closure", "packet": constant_proof + [constant_closure], "accept": True},
        {"name": "false_computation", "packet": [COMPUTE, [box_zero, ONE]], "accept": False},
        {"name": "malformed_successor_counter", "packet": [COMPUTE, [[[0, 0], 0, 0], 0]], "accept": False},
        {"name": "malformed_computation_goal", "packet": [COMPUTE, []], "accept": False},
        {"name": "forged_equality_source",
         "packet": reflexivity_instructions(ONE) + [COMPUTE,
                    [valid_equation, ONE, 0, [1, ONE]], [0, ONE]],
         "accept": False, "guard": "equality_source"},
        {"name": "forged_equality_target",
         "packet": [COMPUTE, COMPUTE,
                    [valid_equation, box_zero, ONE, [1, 0]], [ONE, 0]],
         "accept": False, "guard": "equality_target"},
        {"name": "forged_closure_source",
         "packet": [COMPUTE] + threshold_proof +
                   [[threshold_closure, ONE, 0, threshold_body], [[0, 0, ONE], ONE]],
         "accept": False, "guard": "closure_source"},
        {"name": "forged_closure_motive",
         "packet": [COMPUTE] + constant_proof +
                   [[constant_closure, 0, ONE, [[5, 0, ONE], 0]], [[ONE, 0, ONE], 0]],
         "accept": False, "guard": "closure_motive"},
        {"name": "unproved_major",
         "packet": [COMPUTE, [[box_zero, ONE], box_zero, ONE, [1, 0]], [ONE, 0]],
         "accept": False, "guard": "major_proof"},
        {"name": "free_future_parameter",
         "packet": [COMPUTE, [[0, -1, 0], -1]],
         "accept": False, "guard": "root_scope"},
        {"name": "used_future_witness",
         "packet": [[0, 0, 0, -1], [0, 0, [3, 3]]],
         "accept": False, "guard": "image_scope"},
        {"name": "unused_future_update_is_checked",
         "packet": [COMPUTE, [[0, 0, -1], 0]], "accept": False},
        {"name": "unused_endpoint_payloads",
         "packet": [[0, {"unused": True}, "unused", 0], valid_equation], "accept": True},
    ]
    return copy.deepcopy(cases)


def ns_from_text(source):
    tree = ast.parse(source)
    nodes = []
    for node in tree.body:
        if isinstance(node, ast.Try):
            break
        nodes.append(node)
    ns = {}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), "<focused-kernel>", "exec"), ns)
    return ns


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidate", action="append", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    cases = make_cases()
    rows = []
    for path in args.candidate:
        source = path.read_text()
        ns = ns_from_text(source)
        for case in cases:
            result = run(ns, case["packet"], True)
            if result["accepted"] != case["accept"]:
                raise AssertionError((path.name, case["name"], result))
            rows.append({"program": path.name, "case": case["name"], "passed": True})

    source = args.candidate[0].read_text()
    mutations = {
        "equality_source": ("([s, u], not s and [t])", "([m[0], u], not s and [t])"),
        "equality_target": ("([s, u], not s and [t])", "([s, m[-1]], not s and [t])"),
        "closure_source": ("not s and [t]", "[t]"),
        "closure_motive": ("not s and [t]", "not s and m"),
        "major_proof": ("        c(m, g)\n", "        pass\n"),
        "root_scope": ("if i(a) in g:", "if a in g:"),
        "image_scope": ("d % 2 and i(t, d=1)", "d % 2 and t"),
    }
    probes = []
    for case in cases:
        if "guard" not in case:
            continue
        guard = case["guard"]
        before, after = mutations[guard]
        if source.count(before) != 1:
            raise AssertionError(("Unexpected mutation match count", guard))
        altered = source.replace(before, after)
        result = run(ns_from_text(altered), case["packet"], True)
        if not result["accepted"]:
            raise AssertionError(("Guard probe did not expose altered behavior", guard, result))
        probes.append({"guard": guard, "case": case["name"],
                       "correct_rejects": True, "guard_removed_accepts": True,
                       "mutant_sha256": hashlib.sha256(altered.encode()).hexdigest()})

    jobs = []
    for path in args.candidate:
        for optimized in (False, True):
            for case in cases:
                jobs.append((path, optimized, case["name"],
                             json.dumps(case["packet"]), case["accept"]))
            for label, text in (("empty_input", ""), ("broken_json", "{"),
                                ("null_packet", "null"), ("object_packet", "{}")):
                jobs.append((path, optimized, label, text, False))

    def cli(job):
        path, optimized, label, text, expected = job
        command = [sys.executable] + (["-O"] if optimized else []) + [str(path)]
        result = subprocess.run(command, input=text, text=True,
                                capture_output=True, timeout=20)
        if (result.returncode != (0 if expected else 1)
                or result.stdout != ("ACCEPT\n" if expected else "REJECT\n")
                or expected and result.stderr):
            raise AssertionError(("Focused public-interface failure", path.name,
                                  optimized, label, result.returncode,
                                  result.stdout, result.stderr[:400]))
        return {"program": path.name, "optimized": optimized,
                "case": label, "passed": True}

    with ThreadPoolExecutor(max_workers=8) as pool:
        public_results = list(pool.map(cli, jobs))

    report = {"status": "PASS", "case_count": len(cases),
              "positive_cases": sum(case["accept"] for case in cases),
              "negative_cases": sum(not case["accept"] for case in cases),
              "correct_kernel_runs": len(rows), "guard_probes": probes,
              "public_interface_runs": len(public_results),
              "sources": {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in args.candidate}, "results": rows,
              "public_results": public_results}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    args.output.with_name("focused_cases.json").write_text(json.dumps({"cases": cases}, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("results", "sources", "public_results")}, indent=2))


if __name__ == "__main__":
    main()
