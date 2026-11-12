"""Reproduce typed-kernel checks, ancillary checks, and full-source metrics."""
import ast
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize
import zlib

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / "tests"


def execute(path, data, optimized):
    command = [sys.executable, "-B"] + (["-O"] if optimized else []) + [str(path)]
    result = subprocess.run(command, input=data, capture_output=True, timeout=15)
    return result.returncode == 0 and result.stdout == b"ACCEPT\n"


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def measurements():
    ignored = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
               tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
               tokenize.ENDMARKER}
    files = list((ROOT / "code").glob("*_checker.py"))
    files += list((ROOT / "code" / "ancillary").glob("*.py"))
    files += list((HERE / "ancillary" / "reference").glob("*.py"))
    rows = []
    compressed = ROOT / "code" / "compressed"
    compressed.mkdir(exist_ok=True)
    for path in sorted(files):
        raw = path.read_bytes()
        tree = ast.parse(raw)
        for node in ast.walk(tree):
            if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                if (node.body and isinstance(node.body[0], ast.Expr)
                        and isinstance(node.body[0].value, ast.Constant)
                        and isinstance(node.body[0].value.value, str)):
                    node.body.pop(0)
        normalized = (ast.unparse(tree) + "\n").encode()
        source_gzip = gzip.compress(raw, compresslevel=9, mtime=0)
        normalized_gzip = gzip.compress(normalized, compresslevel=9, mtime=0)
        relative = path.relative_to(ROOT).as_posix()
        rows.append({"file": relative,
            "significant_tokens": sum(t.type not in ignored for t in
                tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
            "ast_nodes": len(list(ast.walk(ast.parse(normalized)))),
            "raw_bytes": len(raw), "normalized_bytes": len(normalized),
            "gzip9_raw_bytes": len(source_gzip),
            "gzip9_normalized_bytes": len(normalized_gzip),
            "sha256_raw": hashlib.sha256(raw).hexdigest(),
            "sha256_normalized": hashlib.sha256(normalized).hexdigest()})
        if relative.startswith("code/"):
            (compressed / (relative.replace("/", "_") + ".normalized.gz")).write_bytes(normalized_gzip)
    return rows


def main():
    producer = load_module("case_producer", HERE / "generate_cases.py")
    producer.build()
    outcomes = []
    for case in json.loads((HERE / "cases.json").read_text()):
        data = (HERE / "certificates" / case["file"]).read_bytes()
        for system, expected in case["expected"].items():
            checker = ROOT / "code" / (system + "_checker.py")
            for optimized in (False, True):
                outcomes.append({"family": "typed", "checker": system,
                    "case": case["file"], "optimized": optimized,
                    "expected": expected, "accepted": execute(checker, data, optimized)})
    for system in ("orbit", "native", "witness"):
        for data in (b"{", b"[]"):
            for optimized in (False, True):
                outcomes.append({"family": "input", "checker": system,
                    "case": data.decode(), "optimized": optimized,
                    "expected": False,
                    "accepted": execute(ROOT / "code" / (system + "_checker.py"), data, optimized)})
    for case in json.loads((HERE / "ancillary" / "cases.json").read_text()):
        data = (HERE / "ancillary" / "certificates" / case["file"]).read_bytes()
        checker = ROOT / "code" / "ancillary" / case["checker"]
        for optimized in (False, True):
            outcomes.append({"family": "ancillary", "checker": case["checker"],
                "case": case["file"], "optimized": optimized,
                "expected": case["expected"], "accepted": execute(checker, data, optimized)})

    orbit = load_module("orbit", ROOT / "code" / "orbit_checker.py")
    rule_outcomes = []
    for case in json.loads((HERE / "open_sequents.json").read_text()):
        scope = case["scope"]
        if not all(orbit.formula(a, scope) for a in case["context"] + [case["goal"]]):
            raise RuntimeError("Ill-formed unit sequent")
        try:
            result = orbit.derive(case["proof"], tuple(case["context"]), scope)
            accepted = result == case["goal"]
        except (ValueError, TypeError, IndexError):
            accepted = False
        rule_outcomes.append({"name": case["name"], "expected": case["expected"],
                              "accepted": accepted, "scope": "Open sequent with displayed assumptions"})
    substitution_checks = [
        (orbit.lift(["i", ["v", 0], 0, ["v", 0]]),
         ["i", ["v", 1], 0, ["v", 0]]),
        (orbit.instance(["q", ["=", ["v", 0], ["v", 1]]], ["s", ["v", 0]]),
         ["q", ["=", ["v", 0], ["s", ["v", 1]]]]),
        (orbit.instance(["d", ["=", ["v", 1], ["v", 2]]], ["s", ["v", 0]]),
         ["d", ["=", ["v", 1], ["s", ["v", 2]]]]),
        (orbit.fresh_instance(["=", ["v", 0], ["v", 1]], ["s", ["v", 0]]),
         ["=", ["s", ["v", 0]], ["v", 1]]),
    ]
    if any(actual != expected for actual, expected in substitution_checks):
        raise RuntimeError("Capture-avoidance control failed")
    failures = [r for r in outcomes + rule_outcomes if r["accepted"] != r["expected"]]
    evidence = ROOT / "evidence"
    evidence.mkdir(exist_ok=True)
    metrics = {"python": sys.version, "zlib": zlib.ZLIB_VERSION,
        "normalization": "Remove genuine docstrings; ast.unparse plus one LF; entire standalone module",
        "gzip": "gzip.compress(data, compresslevel=9, mtime=0); informational only",
        "matched_control_notice": "native_checker and witness_checker are new matched implementations of the pinned NPrf and WPrf rules, not upstream Python files.",
        "ancillary_notice": "The 256/278/521 envelope concerns three implementations of the inherited guarded-source calculus, not orbit_checker.",
        "measurements": measurements()}
    (evidence / "checker_metrics.json").write_text(json.dumps(metrics, indent=2) + "\n")
    report = {"process_checks": len(outcomes),
        "expected_acceptances": sum(r["expected"] for r in outcomes),
        "expected_rejections": sum(not r["expected"] for r in outcomes),
        "open_sequent_checks": len(rule_outcomes),
        "capture_avoidance_checks": len(substitution_checks),
        "failures": failures,
        "scope": "Finite executable controls, not a proof-assistant verification of the metatheorems.",
        "process_outcomes": outcomes, "rule_outcomes": rule_outcomes}
    (evidence / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in
                    ("process_outcomes", "rule_outcomes")}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
