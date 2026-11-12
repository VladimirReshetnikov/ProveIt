"""Reproduce metrics, compile checks, fixture tests and certificate translation.

The tests supplement the written universal simulation proofs.  They are not
a proof assistant formalization of iPRA or of the arithmetic interpretation.
Run: python3 verify.py
"""
import ast
import copy
import hashlib
import io
import json
import random
import subprocess
import sys
import tokenize
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from translate_inferred import translate


ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
PROGRAMS = ["checker_tokens.py", "checker_ast.py", "checker_bytes.py",
            "checker_bytes_readable_decrement.py", "checker_native.py",
            "controls/checker_tokens_256.py", "controls/checker_ast_278.py",
            "controls/checker_bytes_506.py", "controls/checker_native_656.py"]


def metric(name):
    source = (ROOT / name).read_text()
    compile(source, name, "exec")  # ast.parse alone misses some Python restrictions.
    normalized = ast.unparse(ast.parse(source)) + "\n"
    return {"file": name, "bytes": len(normalized.encode()),
            "tokens": sum(t.type not in SKIP for t in
                          tokenize.generate_tokens(io.StringIO(normalized).readline)),
            "ast_nodes": len(list(ast.walk(ast.parse(normalized)))),
            "sha256": hashlib.sha256(source.encode()).hexdigest()}


def cli(name, data, optimized=False):
    command = [sys.executable] + (["-O"] if optimized else []) + [str(ROOT / name)]
    run = subprocess.run(command, input=json.dumps(data), text=True,
                         capture_output=True, timeout=8)
    return run.returncode == 0 and run.stdout == "ACCEPT\n"


def fixture_case(item):
    fixture, candidate, control, optimized = item
    data = json.loads(fixture.read_text())
    old, new = cli(control, data, optimized), cli(candidate, data, optimized)
    return {"fixture": fixture.name, "candidate": candidate,
            "control": control, "optimized": optimized,
            "control_accepts": old, "candidate_accepts": new, "agrees": old == new}


def extracted_program(name):
    """Keep the exact function ASTs, replacing only external JSON acquisition."""
    tree = ast.parse((ROOT / name).read_text())
    nodes = [n for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom, ast.FunctionDef))
             or (isinstance(n, ast.Assign) and len(n.targets) == 1
                 and isinstance(n.targets[0], ast.Name) and n.targets[0].id == "k")]
    return compile(ast.Module(body=nodes, type_ignores=[]), name, "exec")


def execute_extracted(code, data, native=False):
    namespace = {}
    exec(code, namespace)
    stack = copy.deepcopy(data)
    namespace["q"] = stack.pop
    try:
        goal = stack.pop()
        if native:
            namespace["c"](goal, v=1)
        else:
            namespace["c"](goal)
    except Exception:
        return False, len(stack)
    return True, len(stack)


def scan_function(name):
    tree = ast.parse((ROOT / name).read_text())
    checker = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == "c")
    opening = checker.body[0]
    namespace = {"c": object()}
    function = ast.parse("def scan(a, t=None, d=0, k=0, v=0):\n    pass\n").body[0]
    function.body = [opening, ast.parse("return i(a,t,d)").body[0]]
    module = ast.fix_missing_locations(ast.Module(body=[function], type_ignores=[]))
    exec(compile(module, name + ":scan", "exec"), namespace)
    return namespace["scan"]


def scan_result(scan, a, image, depth, floor, mode):
    try:
        return True, repr(scan(copy.deepcopy(a), copy.deepcopy(image), depth, floor, mode))
    except Exception:
        return False, "rejected"


def main():
    metrics = [metric(name) for name in PROGRAMS]
    fixtures = sorted(p for p in (ROOT / "fixtures").glob("*.json")
                      if not p.name.startswith("inferred_major_"))
    jobs = []
    for fixture in fixtures:
        pairs = ([('checker_tokens.py', 'controls/checker_tokens_256.py')]
                 if fixture.stem.endswith("global") else
                 [('checker_ast.py', 'controls/checker_ast_278.py'),
                  ('checker_readable.py', 'controls/checker_ast_278.py'),
                  ('checker_bytes.py', 'controls/checker_bytes_506.py'),
                  ('checker_bytes_readable_decrement.py', 'controls/checker_bytes_506.py'),
                  ('checker_native.py', 'controls/checker_native_656.py')])
        jobs.extend((fixture, candidate, control, optimized)
                    for candidate, control in pairs for optimized in (False, True))
    with ThreadPoolExecutor(max_workers=4) as pool:
        fixture_results = list(pool.map(fixture_case, jobs))
    if not all(r["agrees"] for r in fixture_results):
        raise RuntimeError("a fixture comparison failed")

    translations = []
    for protocol, candidate, control in (
        ("local", "checker_ast.py", "controls/checker_ast_278.py"),
        ("global", "checker_tokens.py", "controls/checker_tokens_256.py")):
        for fixture in fixtures:
            if not fixture.stem.endswith(protocol):
                continue
            data = json.loads(fixture.read_text())
            if not cli(candidate, data):
                continue
            reconstructed, trace = translate(data, protocol)
            if not cli(control, reconstructed):
                raise RuntimeError("a translated accepted certificate was rejected")
            translations.append({"fixture": fixture.name, **trace})

    new_protocol_cases = []
    for protocol, candidate, control in (
        ("local", "checker_ast.py", "controls/checker_ast_278.py"),
        ("global", "checker_tokens.py", "controls/checker_tokens_256.py")):
        data = json.loads((ROOT / "fixtures" / ("inferred_major_" + protocol + ".json")).read_text())
        rebuilt, trace = translate(data, protocol)
        results = {"candidate_accepts_zero_placeholder": cli(candidate, data),
                   "control_accepts_zero_placeholder": cli(control, data),
                   "control_accepts_reconstruction": cli(control, rebuilt)}
        if results != {"candidate_accepts_zero_placeholder": True,
                       "control_accepts_zero_placeholder": False,
                       "control_accepts_reconstruction": True}:
            raise RuntimeError("the inferred-major demonstration failed")
        new_protocol_cases.append({"protocol": protocol, **results, **trace})

    rng = random.Random(20261112)
    leaves = [-8, -3, -1, 0, 1, 2, 3, 5, 9, True, False,
              -0.5, 0.0, 1.5, "", "a", None, {}]

    def random_tree(depth=3):
        if depth and rng.random() < .42:
            return [random_tree(depth - 1) for _ in range(rng.randrange(5))]
        return copy.deepcopy(rng.choice(leaves))

    old_scan = scan_function("controls/checker_native_656.py")
    new_scan = scan_function("checker_native.py")
    scan_count = 10000
    for _ in range(scan_count):
        arguments = (random_tree(), random_tree(), rng.randrange(10),
                     -rng.randrange(4), rng.randrange(2))
        if scan_result(old_scan, *arguments) != scan_result(new_scan, *arguments):
            raise RuntimeError("a validation/opening comparison failed")

    old_code = extracted_program("controls/checker_bytes_506.py")
    new_code = extracted_program("checker_bytes.py")
    originals = [json.loads(p.read_text()) for p in fixtures if p.stem.endswith("local")]
    mutations = 1200
    mutation_accepts = 0
    for _ in range(mutations):
        data = copy.deepcopy(rng.choice(originals))
        if data:
            index = rng.randrange(len(data))
            if isinstance(data[index], list) and data[index] and rng.random() < .7:
                data[index][rng.randrange(len(data[index]))] = random_tree(2)
            else:
                data[index] = random_tree(2)
        before = execute_extracted(old_code, data)
        after = execute_extracted(new_code, data)
        if before != after:
            raise RuntimeError("a truth-valued-checker mutation comparison failed")
        mutation_accepts += before[0]

    report = {"python": sys.version, "metrics": metrics,
              "cli_comparisons": len(fixture_results),
              "cli_processes": 2 * len(fixture_results),
              "fixture_results": fixture_results,
              "translated_accepted_fixtures": len(translations),
              "translations": translations, "new_protocol_cases": new_protocol_cases,
              "validation_opening_comparisons": scan_count,
              "byte_checker_mutation_comparisons": mutations,
              "byte_checker_mutation_accepts": mutation_accepts,
              "status": "PASS"}
    (ROOT / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "metrics": metrics,
                      "cli_comparisons": len(fixture_results),
                      "translated_accepted_fixtures": len(translations),
                      "validation_opening_comparisons": scan_count,
                      "byte_checker_mutation_comparisons": mutations}, indent=2))


if __name__ == "__main__":
    main()
