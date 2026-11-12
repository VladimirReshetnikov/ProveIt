"""Reproduce source provenance, complete-module measurements and acceptance checks."""

import ast
import copy
import gzip
import hashlib
import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {
    tokenize.ENDMARKER, tokenize.ENCODING, tokenize.NEWLINE,
    tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}
PROFILES = {
    "control": ("baseline/native656.py", "c", "q"),
    "primary": ("code/checker.py", "c", "q"),
    "portable": ("code/checker_portable.py", "c", "q"),
    "readable": ("code/readable_checker.py", "check", "instruction"),
    "list_one_shot": ("code/checker_list.py", "c", "q"),
}


def functions(relative):
    path = ROOT / relative
    tree = ast.parse(path.read_text())
    tree.body = [
        node for node in tree.body
        if isinstance(node, (ast.Import, ast.ImportFrom, ast.FunctionDef))
    ]
    namespace = {}
    exec(compile(tree, str(path), "exec"), namespace)
    return namespace


NAMESPACES = {name: functions(path) for name, (path, _, _) in PROFILES.items()}


def invoke(name, goal):
    function = NAMESPACES[name][PROFILES[name][1]]
    if name == "control":
        function(goal, v=1)
    elif name == "list_one_shot":
        # Its documented interface is a fresh standalone process, not a
        # repeatedly callable function with a persistent mutable default.
        function(goal, g=[])
    else:
        function(goal)


class FirstPacket(Exception):
    pass


def stop():
    raise FirstPacket


def first_scan(name, goal):
    NAMESPACES[name][PROFILES[name][2]] = stop
    try:
        invoke(name, goal)
        return True
    except FirstPacket:
        return True
    except (Exception, RecursionError):
        return False


def trace(name, certificate):
    stack = copy.deepcopy(certificate)
    try:
        NAMESPACES[name][PROFILES[name][2]] = stack.pop
        invoke(name, stack.pop())
        return True, len(stack)
    except (Exception, RecursionError):
        return False, None


def same_traces(certificate, names=None):
    names = list(PROFILES) if names is None else names
    results = {name: trace(name, certificate) for name in names}
    assert len(set(results.values())) == 1, results
    return results[names[0]]


def measure(relative):
    path = ROOT / relative
    raw = path.read_bytes()
    tree = ast.parse(raw.decode())
    normalized = (ast.unparse(tree) + "\n").encode()
    return {
        "file": relative,
        "significant_tokens": sum(
            token.type not in SKIP for token in tokenize.generate_tokens(
                io.StringIO(normalized.decode()).readline
            )
        ),
        "ast_nodes": sum(1 for _ in ast.walk(tree)),
        "normalized_bytes": len(normalized),
        "gzip9_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        "sha256": hashlib.sha256(raw).hexdigest(),
    }


def cli(relative, payload, optimized=False):
    command = [sys.executable, "-I", "-S", "-B"]
    if optimized:
        command.append("-O")
    result = subprocess.run(
        command + [str(ROOT / relative)], input=payload,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30,
    )
    return result.returncode == 0 and result.stdout == b"ACCEPT\n"


def main():
    mathematical_provenance = json.loads((ROOT / "PROVENANCE.json").read_text())
    for record in mathematical_provenance["baseline_files"]:
        raw = (ROOT / record["local_path"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == record["sha256"]
        blob = b"blob " + str(len(raw)).encode() + b"\0" + raw
        assert hashlib.sha1(blob).hexdigest() == record["git_blob_sha1"]
    baseline_metrics = [measure(str(path.relative_to(ROOT)))
                        for path in sorted((ROOT / "baseline").glob("*.py"))]
    (ROOT / "evidence/baseline_metrics.json").write_text(
        json.dumps({"python": sys.version, "programs": baseline_metrics}, indent=2) + "\n")
    provenance = json.loads((ROOT / "IMPLEMENTATION_PROVENANCE.json").read_text())
    for record in provenance["files"]:
        raw = (ROOT / record["local_path"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == record["sha256"]
        blob = b"blob " + str(len(raw)).encode() + b"\0" + raw
        assert hashlib.sha1(blob).hexdigest() == record["git_blob_sha1"]

    rng = random.Random(62396643)
    leaves = [
        None, False, True, {}, {"a": 0}, "", "x", "0", [],
        -4, -1, 0, 1, 2, 3, 4, 5, 6, 7, 15, 255,
        2 ** 100 + 1, -(2 ** 100),
        -0.5, 0.0, 1.0, 3.0, float("nan"), float("inf"),
        -float("inf"), [0], [3], [0, 0], [0, [0]], [0, 0, 0],
    ]

    def arbitrary(depth):
        if not depth or rng.randrange(3) == 0:
            return copy.deepcopy(rng.choice(leaves))
        return [arbitrary(depth - 1) for _ in range(rng.randrange(6))]

    def term(depth, fuel):
        if not fuel or rng.randrange(3) == 0:
            return rng.choice([0] + list(range(3, max(4, depth + 4), 2)))
        if rng.randrange(2):
            return [term(depth + 4, fuel - 1)]
        return [term(depth + 2, fuel - 1) for _ in range(3)]

    def formula(depth, fuel):
        if not fuel or rng.randrange(2):
            return [term(depth + 3, 3), term(depth + 3, 3)]
        return [formula(depth + 4, fuel - 1)]

    goals = leaves + [arbitrary(5) for _ in range(2000)]
    goals += [formula(0, 4) for _ in range(2000)]
    deep_goals = []
    for binders in (1, 2, 8, 32, 64, 96):
        for value in (4 * binders + 1, 4 * binders + 3, -1, True, 3.0):
            goal = [value, value]
            for _ in range(binders):
                goal = [goal]
            deep_goals.append(goal)
    goals += deep_goals
    for goal in goals:
        results = {name: first_scan(name, goal) for name in PROFILES}
        assert len(set(results.values())) == 1, (goal, results)

    # The namespaces above are deliberately reused. This alternation also
    # tests that successful public entries cannot disable the next entry's
    # validator in the primary's immutable default context.
    repeated = [[0, 0], [False, False], [0, [0]], [0.0, 0.0]] * 20
    for goal in repeated:
        assert first_scan("control", goal) == first_scan("primary", goal)

    cases = json.loads((ROOT / "validation/fixtures/cases.json").read_text())
    native_accept = {
        "compound_case_introduction_local",
        "compound_implication_elimination_local",
        "computation_successor_local", "computation_zero_local",
        "derived_zero_source_equational_transport_local",
        "guarded_induction_with_used_hypothesis_local",
        "guarded_lift_elimination_local",
        "guarded_literal_equation_introduction_local",
        "transport_reflexivity_local", "zero_symmetry_all_numbers_local",
        "zero_symmetry_computable_zero_local", "zero_symmetry_one_local",
        "old_atomic_case_local",
    }
    traces = []
    cli_results = []
    for case in cases:
        payload = (ROOT / "validation/fixtures" / case["file"]).read_bytes()
        certificate = json.loads(payload)
        outcome = same_traces(certificate)
        expected = case["name"] in native_accept
        assert outcome[0] == expected, (case["name"], outcome, expected)
        traces.append({"case": case["name"], "accepted": outcome[0],
                       "unused_prefix_entries": outcome[1]})
        for optimized in (False, True):
            for name in ("control", "primary", "readable"):
                accepted = cli(PROFILES[name][0], payload, optimized)
                assert accepted == expected, (case["name"], name, optimized)
                cli_results.append({"case": case["name"], "profile": name,
                                    "optimized": optimized, "accepted": accepted})

    prefix = [None, "unused", {"unused": [False, 0.5]}, 2 ** 100]
    good = json.loads((ROOT / "validation/fixtures/computation_zero_local.json").read_text())
    assert same_traces(prefix + good) == (True, len(prefix))

    small = [json.loads((ROOT / "validation/fixtures" / name).read_text()) for name in (
        "computation_zero_local.json", "computation_successor_local.json",
        "compound_case_introduction_local.json", "transport_reflexivity_local.json",
    )]

    def addresses(tree, prefix=()):
        result = [prefix]
        if isinstance(tree, list):
            for index, child in enumerate(tree):
                result += addresses(child, prefix + (index,))
        return result

    for _ in range(256):
        certificate = copy.deepcopy(rng.choice(small))
        path = rng.choice(addresses(certificate))
        replacement = copy.deepcopy(rng.choice(leaves))
        if not path:
            certificate = replacement
        else:
            parent = certificate
            for index in path[:-1]:
                parent = parent[index]
            parent[path[-1]] = replacement
        same_traces(certificate)

    malformed_payloads = [b"null", b"false", b"0", b'"text"', b"{}", b"[]", b"["]
    for payload in malformed_payloads:
        for name in ("control", "primary"):
            assert not cli(PROFILES[name][0], payload)

    measured = [measure(value[0]) for value in PROFILES.values()]
    (ROOT / "evidence").mkdir(exist_ok=True)
    metrics = {"python": sys.version, "modules": measured}
    report = {
        "python": sys.version, "all_passed": True,
        "public_goal_comparisons": len(goals),
        "public_goal_profiles": len(PROFILES),
        "deep_scope_cases": len(deep_goals),
        "repeated_public_entries": len(repeated),
        "complete_fixture_comparisons": len(traces),
        "complete_fixture_profiles": len(PROFILES),
        "certificate_mutation_comparisons": 256,
        "unused_prefix_comparisons": 1,
        "cli_processes": len(cli_results) + 2 * len(malformed_payloads),
        "native_fixture_accepted": len(native_accept),
        "native_fixture_rejected": len(cases) - len(native_accept),
        "traces": traces, "cli_checks": cli_results,
        "scope": "Finite tests supplement paper/checker_equivalence.txt; no new proof-assistant formalization.",
    }
    (ROOT / "evidence/metrics.json").write_text(json.dumps(metrics, indent=2) + "\n")
    (ROOT / "evidence/validation.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("traces", "cli_checks")}, indent=2))


if __name__ == "__main__":
    main()
