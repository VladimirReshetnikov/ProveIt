"""Reproduce the three complete-source bounds and concrete checking evidence.

Only standard Python is required.  Finite tests support the implementation;
they are not formal proofs of bi-interpretability or absolute minimality.
"""
from pathlib import Path
import ast
import concurrent.futures
import copy
import hashlib
import importlib.util
import json
import platform
import random
import subprocess
import sys

from translate import endpoints_only, translate

ROOT = Path(__file__).resolve().parent
PROFILES = ("tokens", "structure", "bytes")


def module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


MEASURE = module(ROOT / "reference/source_measure.py", "source_measure")


def core(path):
    tree = ast.parse(path.read_text())
    tree.body = [n for n in tree.body if isinstance(n, (
        ast.Import, ast.ImportFrom, ast.Assign, ast.FunctionDef))]
    return compile(ast.fix_missing_locations(tree), str(path), "exec")


PATHS = {p: ROOT / ("selected_" + p + ".py") for p in PROFILES}
PATHS.update({"readable_unfocused": ROOT / "readable_unfocused.py",
              "readable_focused": ROOT / "readable_focused.py",
              "old_unfocused": ROOT / "reference/classic_checker.py",
              "old_focused": ROOT / "reference/focused_checker.py"})
CORES = {key: core(path) for key, path in PATHS.items()}


def run(kind, packet):
    namespace = {}
    exec(CORES[kind], namespace)
    data = copy.deepcopy(packet)
    try:
        namespace["q"] = data.pop
        goal = namespace["q"]()
        if kind in ("bytes", "old_focused"):
            goal = namespace["i"](goal)
        elif kind == "readable_focused":
            goal = namespace["opening"](goal)
        entry = namespace.get("c", namespace.get("check"))
        answer = entry(goal, [])
        success = bool(answer) if kind.startswith("old_") else True
    except BaseException:
        success = False
    return success, namespace["k"], data


def paths(value):
    yield ()
    if isinstance(value, list):
        for index, child in enumerate(value):
            for rest in paths(child):
                yield (index,) + rest


def replace(value, path, replacement):
    if not path:
        return copy.deepcopy(replacement)
    result = copy.deepcopy(value)
    at = result
    for index in path[:-1]:
        at = at[index]
    at[path[-1]] = copy.deepcopy(replacement)
    return result


def compare(profile, packet):
    control = "readable_focused" if profile == "bytes" else "readable_unfocused"
    actual = run(profile, packet)
    expected = run(control, packet)
    if actual[0] != expected[0] or actual[0] and actual[1:] != expected[1:]:
        raise AssertionError(("Explicit-guard discrepancy", profile, packet, actual, expected))
    return actual[0]


def cli(job):
    profile, optimized, case = job
    process = subprocess.run([sys.executable] + (["-O"] if optimized else []) +
                             [str(PATHS[profile])], input=json.dumps(case["packet"]),
                             text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             timeout=15)
    expected = ("ACCEPT\n", 0) if case["accept"] else ("REJECT\n", 1)
    if (process.stdout, process.returncode) != expected:
        raise AssertionError(("CLI", profile, optimized, case["name"],
                              process.stdout, process.returncode, process.stderr))
    return 1


def main():
    evidence = ROOT / "evidence"
    evidence.mkdir(exist_ok=True)
    provenance = json.loads((ROOT / "provenance.json").read_text())
    for item in provenance["sources"]:
        raw = (ROOT / item["local_file"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == item["sha256"]
    cases = {p: [] for p in PROFILES}
    translation_stats = {}
    for focused in (False, True):
        label = "focused" if focused else "unfocused"
        inputs = json.loads((ROOT / ("fixtures/input_" + label + ".json")).read_text())["cases"]
        outputs = []
        for case in inputs:
            if run("old_" + label, case["packet"])[0] != case["accept"]:
                raise AssertionError(("Inherited fixture mismatch", label, case["name"]))
            if case["accept"]:
                packet, stats = translate(case["packet"], focused=focused)
                outputs.append({"name": label + "/" + case["name"],
                                "packet": packet, "accept": True, "translation": stats})
        translation_stats[label] = {
            "original_cases_replayed": len(inputs), "positive_cases_translated": len(outputs),
            "old_allocations": sum(c["translation"]["old_allocations"] for c in outputs),
            "new_allocations": sum(c["translation"]["new_allocations"] for c in outputs),
        }
        (ROOT / ("fixtures/translated_" + label + ".json")).write_text(
            json.dumps({"cases": outputs}, indent=2) + "\n")
        for p in (["bytes"] if focused else ["tokens", "structure"]):
            cases[p].extend(outputs)

    fresh = json.loads((ROOT / "fixtures/input_uniform_focused_tests.json").read_text())["cases"]
    fresh = [{**c, "name": "uniform/" + c["name"], "packet": endpoints_only(c["packet"])} for c in fresh]
    endpoint_bad = [c for c in json.loads((ROOT / "fixtures/input_endpoint_tests.json").read_text())["cases"]
                    if not c["accept"]]
    common_bad = [{"name": "bad/" + c["name"], **{k: v for k, v in c.items() if k != "name"}}
                  for c in endpoint_bad]
    common_bad += [{"name": "bad/empty", "packet": [], "accept": False},
                   {"name": "bad/false_equation", "packet": [[[0], 0]], "accept": False},
                   {"name": "bad/non_array", "packet": {}, "accept": False}]
    for p in PROFILES:
        cases[p].extend(common_bad)
        # Truth-shortcut tests use hypothesis closure, which the focused
        # presentation deliberately omits.  Its own translated corpus is
        # used instead, together with the common malformed/false inputs.
        if p != "bytes":
            cases[p].extend(fresh)
        for case in cases[p]:
            if compare(p, case["packet"]) != case["accept"]:
                raise AssertionError(("Fixture", p, case["name"]))

    rng = random.Random(202611101709)
    replacements = [None, False, True, -1000, -3, -1, 0, 1, 2, 4, 100,
                    -0.5, 0.5, 1.5, "", "x", {}, {"x": 1}, [], [0],
                    [0, 0], [0, 0, 0], [0, 0, 0, 0]]
    mutation_comparisons = 0
    for p in PROFILES:
        for case in cases[p]:
            choices = list(paths(case["packet"]))
            for _ in range(12):
                changed = replace(case["packet"], rng.choice(choices), rng.choice(replacements))
                compare(p, changed)
                mutation_comparisons += 1
    jobs = [(p, optimized, case) for p in PROFILES for optimized in (False, True) for case in cases[p]]
    with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
        cli_runs = sum(pool.map(cli, jobs))
    metrics = {p: MEASURE.metrics(PATHS[p]) for p in PROFILES}
    old_metrics = {p: MEASURE.metrics(ROOT / ("reference/old_" + p + ".py")) for p in PROFILES}
    fields = ("normalized_tokens", "ast_nodes", "normalized_bytes")
    receipt = {
        "python": platform.python_version(), "source_snapshot": provenance["commit"],
        "all_passed": True, "translation": translation_stats,
        "selected_fixture_counts": {p: len(cases[p]) for p in PROFILES},
        "explicit_guard_mutation_comparisons": mutation_comparisons,
        "cli_runs": cli_runs, "ordinary_and_optimized_python": True,
        "metrics": metrics, "old_metrics": old_metrics,
        "new_coordinate_envelope": {f: min(m[f] for m in metrics.values()) for f in fields},
        "old_coordinate_envelope": {f: min(m[f] for m in old_metrics.values()) for f in fields},
        "scope": "Complete programs. Each coordinate envelope uses different programs. The controls and finite tests are not a formal soundness proof, a minimality theorem, or a new arithmetic axiomatization."
    }
    (evidence / "validation.json").write_text(json.dumps(receipt, indent=2) + "\n")
    (evidence / "fixtures.json").write_text(json.dumps(cases, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k not in ("metrics", "old_metrics")}, indent=2))


if __name__ == "__main__":
    main()
