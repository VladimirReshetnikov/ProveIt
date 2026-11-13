"""Finite evidence for reader preservation, with unchanged inference kernels.

All control fixtures are replayed normally and with Python -O. The written
proofs establish the universal statements; these subprocess checks support
the implementations. This script is not part of any measured checker.
"""
from pathlib import Path
import ast
import concurrent.futures
import hashlib
import io
import json
import subprocess
import sys
import tokenize

from translate import convert

ROOT = Path(__file__).resolve().parent
PROFILES = [
    ("checker_tokens302.py", "checker_tokens299.py"),
    ("checker_ast340.py", "checker_ast338.py"),
    ("checker_bytes584.py", "checker_bytes575.py"),
]
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
           tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    tree = ast.parse(path.read_text())
    source = ast.unparse(tree) + "\n"
    return {
        "tokens": sum(t.type not in IGNORED for t in
                      tokenize.generate_tokens(io.StringIO(source).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(tree)),
        "normalized_bytes": len(source.encode()),
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
    }


def retained_kernel(path):
    """Keep every inference, scope, and substitution definition verbatim."""
    tree = ast.parse(path.read_text())
    result = []
    for node in tree.body:
        if isinstance(node, ast.FunctionDef):
            result.append(node)
        elif isinstance(node, ast.Assign):
            names = [target.id for target in node.targets
                     if isinstance(target, ast.Name)]
            if any(name in ("i", "k", "v") for name in names):
                result.append(node)
    return ast.dump(ast.Module(body=result, type_ignores=[]))


def run(job):
    relative, name, text, expected, optimized = job
    try:
        completed = subprocess.run(
            [sys.executable, *(["-O"] if optimized else []), str(ROOT / relative)],
            input=text, text=True, capture_output=True, timeout=20,
        )
        accepted = completed.returncode == 0 and completed.stdout == "ACCEPT\n"
        return {"program": relative, "case": name, "optimized": optimized,
                "expected": expected, "accepted": accepted,
                "exit_code": completed.returncode}
    except subprocess.TimeoutExpired:
        return {"program": relative, "case": name, "optimized": optimized,
                "expected": expected, "accepted": False, "timeout": True}


def main():
    jobs = []
    metrics = {}
    source_cases = {}
    expression_cases = {}
    translator_checks = 0
    for old, new in PROFILES:
        control, candidate = ROOT / "controls" / old, ROOT / "code" / new
        if retained_kernel(control) != retained_kernel(candidate):
            raise SystemExit("Inference kernel differs: " + new)
        metrics[new] = {"control": measure(control), "candidate": measure(candidate)}
        cases = json.loads((ROOT / "fixtures" / old.replace(".py", ".json")).read_text())["cases"]
        source_cases[new] = len(cases)
        for case in cases:
            text = json.dumps(case["certificate"])
            for program in ("controls/" + old, "code/" + new):
                jobs.extend((program, "inherited:" + case["name"], text,
                             case["expected"], optimized)
                            for optimized in (False, True))
            if case["expected"]:
                encoded = convert(case["certificate"])
                # The converter does not use eval and preserves the entire data.
                if json.loads(encoded) != case["certificate"]:
                    raise SystemExit("Converter changed a certificate")
                translator_checks += 1
                jobs.extend(("code/" + new, "translated:" + case["name"], encoded,
                             True, optimized) for optimized in (False, True))
        base = next(case["certificate"] for case in cases if case["expected"])
        text = convert(base)
        # These are new spellings of exactly the same integer/list certificate.
        non_json = [
            ("trailing_comma", text[:-1] + ",]"),
            ("outer_list_subscript", "[" + text + "][0]"),
            ("subtracted_index", "[" + text + "][1-1]"),
            ("negative_index", "[0," + text + "][-1]"),
            ("repeated_minus", "[" + text + "][--0]"),
            ("discarded_integer", "[1-2," + text + "][1]"),
        ]
        rejected = [
            ("boolean", "True"), ("false_boolean", "False"),
            ("float", "1.0"), ("exponential_float", "1e0"),
            ("nan", "NaN"), ("json_null", "null"),
            ("string", "'x'"), ("dictionary", "{0:0}"),
            ("name", "x"), ("call", "print(1)"),
            ("import_call", "__import__('os')"),
            ("lambda_call", "(lambda:0)()"),
            ("attribute", "[1].__class__"),
            ("assignment", "x=1"), ("walrus", "(x:=1)"),
            ("comment", text + "# comment"),
            ("semicolon", text + ";0"),
            ("list_comprehension", "[x for x in []]"),
            ("slice", "[1][0:1]"), ("multiplication", "[1]*2"),
            ("unicode_digit", "\u0661"), ("form_feed", "\f" + text),
            ("safe_bad_syntax", "[["), ("safe_int_root", "1-2"),
            ("safe_tuple_root", text + ","),
            ("safe_tuple_index", "[" + text + "][0,]"),
            ("safe_invalid_index", "[][-1]"),
            ("unused_boolean", "[True," + text[1:]),
            ("unused_float", "[1.0," + text[1:]),
            ("unused_call", "[print(1)," + text[1:]),
            ("unused_string", "['x'," + text[1:]),
        ]
        expression_cases[new] = {"valid_new_spellings": len(non_json),
                                 "rejected": len(rejected)}
        for name, expression in non_json:
            jobs.extend(("code/" + new, "expression:" + name, expression, True, optimized)
                        for optimized in (False, True))
        for name, expression in rejected:
            jobs.extend(("code/" + new, "expression:" + name, expression, False, optimized)
                        for optimized in (False, True))
    with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
        results = list(pool.map(run, jobs))
    failures = [row for row in results if row["accepted"] != row["expected"] or row.get("timeout")]
    receipt = {"python": sys.version, "metrics": metrics,
               "unchanged_inference_kernels": True,
               "inherited_cases_per_candidate": source_cases,
               "expression_cases_per_candidate": expression_cases,
               "translator_round_trips": translator_checks,
               "process_runs": len(results), "failures": failures,
               "results": results}
    (ROOT / "evidence" / "verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k != "results"}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
