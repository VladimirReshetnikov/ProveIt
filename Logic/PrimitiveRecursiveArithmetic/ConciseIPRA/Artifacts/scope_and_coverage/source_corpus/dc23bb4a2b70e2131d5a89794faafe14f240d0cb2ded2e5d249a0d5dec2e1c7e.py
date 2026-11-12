"""Independent differential and public-interface replay for explicit fields.

This validation harness and the adapters are outside the trusted kernel.
Finite replay is not a formal soundness or bi-interpretability proof.
"""
import argparse
import ast
import copy
import hashlib
import json
import random
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from convert import convert_packet, erase_packet


def namespace(path):
    tree = ast.parse(path.read_text())
    prefix = []
    for node in tree.body:
        if isinstance(node, ast.Try):
            break
        prefix.append(node)
    if not any(isinstance(n, ast.FunctionDef) and n.name == "c" for n in prefix):
        raise ValueError("No checker in expected source prefix")
    result = {}
    exec(compile(ast.Module(body=prefix, type_ignores=[]), str(path), "exec"), result)
    return result


def run(ns, packet, exception_style=False):
    data = copy.deepcopy(packet)
    ns["k"] = 0
    calls = []
    try:
        def pop():
            calls.append(len(data) - 1)
            return data.pop()
        ns["q"] = pop
        result = ns["c"](pop(), [])
        accepted = True if exception_style else bool(result)
    except BaseException:
        accepted = False
    return {"accepted": accepted, "floor": ns["k"], "popped": calls}


def mutate(packet, rng):
    paths = []
    def visit(value, path):
        paths.append(path)
        if type(value) is list:
            for index, child in enumerate(value):
                visit(child, path + (index,))
    visit(packet, ())
    path = rng.choice(paths)
    choices = [None, False, True, -17, -2, -1, 0, 1, 2, 0.5,
               "", "bad", {}, [], [0], [0, 0], [0, 0, 0], [0, 0, 0, 0]]
    replacement = copy.deepcopy(rng.choice(choices))
    result = copy.deepcopy(packet)
    if not path:
        return replacement
    parent = result
    for index in path[:-1]:
        parent = parent[index]
    parent[path[-1]] = replacement
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--boolean", type=Path)
    parser.add_argument("--exception", type=Path)
    parser.add_argument("--candidate", nargs=2, action="append", default=[],
                        metavar=("NAME", "PATH"))
    parser.add_argument("--legacy-control", nargs=2, action="append", default=[],
                        metavar=("NAME", "PATH"))
    parser.add_argument("--mutation-rounds", type=int, default=12)
    parser.add_argument("--cases", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    paths = {"baseline": args.baseline}
    new_names = []
    if args.boolean:
        paths["boolean"] = args.boolean
        new_names.append("boolean")
    if args.exception:
        paths["exception"] = args.exception
        new_names.append("exception")
    for name, path in args.candidate:
        paths[name] = Path(path)
        new_names.append(name)
    old_names = []
    for name, path in args.legacy_control:
        paths[name] = Path(path)
        old_names.append(name)
    nss = {name: namespace(path) for name, path in paths.items()}
    cases = json.loads(args.cases.read_text())["cases"]
    checks = {"original_fixtures": 0, "converted_fixtures": 0,
              "accepted_trace_comparisons": 0, "old_format_mutations": 0,
              "explicit_format_mutations": 0, "noncanonical_erasure_skips": 0}

    def compare(old, new, expected=None):
        reference = run(nss["baseline"], old)
        if expected is not None and reference["accepted"] != expected:
            raise AssertionError(("Baseline mismatch", expected, reference))
        for name in new_names + old_names:
            packet = old if name in old_names else new
            result = run(nss[name], packet, name != "boolean")
            if result["accepted"] != reference["accepted"]:
                raise AssertionError(("Verdict mismatch", name, old, new,
                                      reference, result))
            if result["accepted"]:
                if result != reference:
                    raise AssertionError(("Accepted trace mismatch", name,
                                          reference, result))
                checks["accepted_trace_comparisons"] += 1
        return reference["accepted"]

    for case in cases:
        compare(case["packet"], convert_packet(case["packet"]), case["accept"])
        checks["original_fixtures"] += 1
        checks["converted_fixtures"] += len(new_names)

    rng = random.Random(20261109)
    for case in cases:
        for _ in range(args.mutation_rounds):
            old = mutate(case["packet"], rng)
            compare(old, convert_packet(old))
            checks["old_format_mutations"] += 1
        converted = convert_packet(case["packet"])
        for _ in range(args.mutation_rounds):
            new = mutate(converted, rng)
            try:
                old = erase_packet(new)
            except ValueError:
                checks["noncanonical_erasure_skips"] += 1
                continue
            compare(old, new)
            checks["explicit_format_mutations"] += 1

    jobs = []
    for case in cases:
        for name, path in paths.items():
            for optimized in (False, True):
                packet = case["packet"] if name == "baseline" or name in old_names else convert_packet(case["packet"])
                jobs.append((name, path, optimized, case["name"], packet, case["accept"]))

    def cli(job):
        name, path, optimized, label, packet, expected = job
        command = [sys.executable] + (["-O"] if optimized else []) + [str(path)]
        result = subprocess.run(command, input=json.dumps(packet), text=True,
                                capture_output=True, timeout=20)
        if (result.returncode != (0 if expected else 1)
                or result.stdout != ("ACCEPT\n" if expected else "REJECT\n")
                or expected and result.stderr):
            raise AssertionError(("Public interface mismatch", name, optimized,
                                  label, result.returncode, result.stdout,
                                  result.stderr[:500]))
        return {"program": name, "optimized": optimized, "case": label,
                "expected_accept": expected, "passed": True}

    with ThreadPoolExecutor(max_workers=8) as pool:
        cli_results = list(pool.map(cli, jobs))
    report = {
        "status": "PASS", "scope": "finite differential and public-interface evidence",
        "seed": 20261109, "mutation_rounds": args.mutation_rounds, "checks": checks,
        "fixture_positive_count": sum(case["accept"] for case in cases),
        "fixture_negative_count": sum(not case["accept"] for case in cases),
        "public_interface_runs": len(cli_results),
        "sources": {name: {"path": str(path.resolve()),
                    "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
                    for name, path in paths.items()},
        "fixture_sha256": hashlib.sha256(args.cases.read_bytes()).hexdigest(),
        "public_results": cli_results,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("public_results", "sources")}, indent=2))


if __name__ == "__main__":
    main()
