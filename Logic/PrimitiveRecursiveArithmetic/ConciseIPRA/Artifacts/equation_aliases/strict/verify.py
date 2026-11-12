"""Check exact source transformations, hashes, and 56 inherited boundary cases.

This is an untrusted reproduction driver. No delivered checker imports it.
"""
import ast
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def canonical(source):
    return ast.unparse(ast.parse(source)) + "\n"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def source_checks():
    source = (ROOT / "controls/context_phase_strict666.py").read_text()
    source = source.replace("int(a) is a and ", "")
    source = source.replace("))) and (i(a) in g or [", ")))(a) in g or [")
    source = source.replace("for m, s, u, t in [q()]])", "for m, s, u, t in [q()]]")
    source = source.replace("(d % 2 and (not a or a > 1 == a % 2))",
                            "d % 2 * (not a or a > 1 == a % 2)")
    source = source.replace("(d % 2 or not g)", "(d % 2 | (not g))")
    require(canonical(source) == (ROOT / "checkers/tokens338.py").read_text(),
            "Token profile is not exactly the documented transformation")
    framed = source.replace(
        "p = json.load(open(0))\nq = not str(p).strip('0123456789-[], ') and p.pop\nc([], q())",
        "c([], (q := not str(p := json.load(open(0))).strip('0123456789-[], ') and p.pop)())")
    require(canonical(framed) == (ROOT / "checkers/ast386.py").read_text(),
            "AST profile is not exactly the documented framing transformation")
    strict = (ROOT / "controls/strict637.py").read_text()
    strict = strict.replace("v <= (d % 2 and (not a or a > 1 == a % 2))",
                            "v <= d % 2 * (not a or a > 1 == a % 2)")
    require(canonical(strict) == (ROOT / "checkers/bytes633.py").read_text(),
            "Byte profile is not exactly the documented one-expression transformation")
    return {"tokens_exact": True, "ast_exact": True, "bytes_exact": True}


def main():
    proofs = source_checks()
    manifest = json.loads((ROOT / "fixtures/manifest.json").read_text())
    programs = sorted((ROOT / "checkers").glob("*.py"))
    results = []
    for item in manifest:
        data = (ROOT / item["file"]).read_bytes()
        require(hashlib.sha256(data).hexdigest() == item["sha256"],
                "Fixture checksum mismatch: " + item["file"])
        for program in programs:
            for optimized in (False, True):
                args = [sys.executable] + (["-O"] if optimized else []) + [str(program)]
                completed = subprocess.run(args, input=data, capture_output=True, timeout=20)
                accepted = completed.returncode == 0 and completed.stdout == b"ACCEPT\n"
                results.append({"file": item["file"], "program": program.name,
                                "optimized": optimized, "expected": item["expected"],
                                "accepted": accepted, "passed": accepted == item["expected"]})
    failures = [row for row in results if not row["passed"]]
    report = {"source_checks": proofs, "fixture_count": len(manifest),
              "executions": len(results), "failures": failures, "results": results}
    (ROOT / "evidence/verification.json").write_text(json.dumps(report, indent=2) + "\n")
    require(not failures, "Unexpected checker outcomes; see evidence/verification.json")
    print(json.dumps({k: v for k, v in report.items() if k != "results"}, indent=2))


if __name__ == "__main__":
    main()
