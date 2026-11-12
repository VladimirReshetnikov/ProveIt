"""Differential validation for composed existing Choice-DI reductions."""
import ast
import copy
import importlib.util
import json
import random
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path


ROOT = Path(__file__).resolve().parent
WORK = ROOT.parent
PROFILES = {"tokens": "tokens.py", "structure": "structure.py", "bytes": "bytes.py"}
COMPARISON = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else ROOT.parent / "comparison"



def namespace(path):
    tree = ast.parse(path.read_text())
    if not isinstance(tree.body[-1], ast.Try):
        raise RuntimeError("Unexpected driver")
    tree.body.pop()
    result = {}
    exec(compile(tree, str(path), "exec"), result)
    return result


def run_in_process(ns, packet):
    data = copy.deepcopy(packet)
    ns["k"] = 0
    try:
        ns["q"] = data.pop
        accepted = bool(ns["c"](data.pop(), []))
    except BaseException:
        accepted = False
    return accepted, ns["k"], data


def cli(job):
    name, path, optimized, case = job
    command = [sys.executable] + (["-O"] if optimized else []) + [str(path)]
    result = subprocess.run(command, input=json.dumps(case["packet"]), text=True,
                            capture_output=True, timeout=20)
    passed = result.stdout == ("ACCEPT\n" if case["accept"] else "REJECT\n")
    passed = passed and result.returncode == (0 if case["accept"] else 1)
    if not passed:
        raise RuntimeError("CLI mismatch: " + name + "/" + case["name"])
    return {"program": name, "optimized": optimized, "case": case["name"],
            "expected_accept": case["accept"], "passed": True}


def mutations(packet, rng):
    paths = []
    def walk(value, path):
        paths.append(path)
        if type(value) is list:
            for index, item in enumerate(value):
                walk(item, path + (index,))
    walk(packet, ())
    replacements = [None, False, True, -7, -1, 0, 1, 2, 4, 0.5,
                    "x", "", {}, [], [0], [0, 0], [0, 0, 0], [0, 0, 0, 0]]
    for _ in range(24):
        path = rng.choice(paths)
        value = copy.deepcopy(packet)
        replacement = copy.deepcopy(rng.choice(replacements))
        if not path:
            value = replacement
        else:
            parent = value
            for index in path[:-1]:
                parent = parent[index]
            parent[path[-1]] = replacement
        yield value


def main():
    source = json.loads((ROOT / "cases.json").read_text())
    cases = source["cases"]
    paths = {}
    namespaces = {}
    for profile, filename in PROFILES.items():
        paths["old_" + profile] = COMPARISON / ("old_" + profile + ".py")
        paths["new_" + profile] = ROOT / filename
    for name, path in paths.items():
        namespaces[name] = namespace(path)

    direct = 0
    for case in cases:
        for name, ns in namespaces.items():
            actual = run_in_process(ns, case["packet"])
            if actual[0] != case["accept"]:
                raise RuntimeError("Fixture mismatch: " + name + "/" + case["name"])
            direct += 1
        for profile in PROFILES:
            old = run_in_process(namespaces["old_" + profile], case["packet"])
            new = run_in_process(namespaces["new_" + profile], case["packet"])
            if old[0] and old != new:
                raise RuntimeError("Accepted trace mismatch: " + profile + "/" + case["name"])

    rng = random.Random(1109)
    differential = 0
    for case in cases:
        for packet in mutations(case["packet"], rng):
            for profile in PROFILES:
                old = run_in_process(namespaces["old_" + profile], packet)
                new = run_in_process(namespaces["new_" + profile], packet)
                if old[0] != new[0] or old[0] and old != new:
                    (ROOT / "counterexample.json").write_text(json.dumps({"packet": packet, "profile": profile, "old": old, "new": new}))
                    raise RuntimeError("Differential mismatch: " + profile)
                differential += 1

    jobs = [(name, path, optimized, case) for name, path in paths.items()
            for optimized in (False, True) for case in cases]
    with ThreadPoolExecutor(max_workers=6) as executor:
        cli_results = list(executor.map(cli, jobs))
    receipt = {"inherited_cases": source["inherited_cases"], "focused_cases": source["focused_cases"],
               "fixture_in_process_checks": direct, "mutation_differential_pairs": differential,
               "public_cli_checks": len(cli_results), "failures": 0,
               "accepted_trace_policy": "Verdict, final freshness floor, and remaining packet data match.",
               "programs": {name: str(path) for name, path in paths.items()},
               "cli": cli_results}
    (ROOT / "validation.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k not in ("programs", "cli")}, indent=2))


if __name__ == "__main__":
    main()
