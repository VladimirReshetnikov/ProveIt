"""Reproduce source sizes, exact rewrites, and finite regression evidence.

Use CPython 3.12.14 for the recorded upstream normalization convention.
No test runner, fixture, translator, or document is imported by a checker.
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

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
EXPECTED = {
    "checkers/strict_tokens299.py": (299, 343, 633),
    "checkers/strict_ast335.py": (308, 335, 667),
    "checkers/strict_bytes583.py": (310, 361, 583),
    "controls/entry_tokens304.py": (304, 349, 646),
    "controls/ast340.py": (314, 340, 681),
    "controls/bytes584.py": (311, 362, 584),
}


def measure(relative):
    raw = (ROOT / relative).read_bytes()
    tree = ast.parse(raw.decode())
    normalized = ast.unparse(tree) + "\n"
    values = (sum(t.type not in SKIP for t in
                  tokenize.generate_tokens(io.StringIO(normalized).readline)),
              len(list(ast.walk(tree))), len(normalized.encode()))
    if values != EXPECTED[relative]:
        raise ValueError(f"Metric mismatch: {relative}: {values}")
    return {"path": relative, "tokens": values[0], "ast_nodes": values[1],
            "normalized_bytes": values[2], "raw_bytes": len(raw),
            "raw_sha256": hashlib.sha256(raw).hexdigest(),
            "normalized_sha256": hashlib.sha256(normalized.encode()).hexdigest()}


def shift(value):
    """Canonical syntax: move every upper coordinate by two; preserve flags."""
    if type(value) is list:
        return [shift(x) for x in value]
    return value + 2 if type(value) is int and value >= 3 else value


def target(document, protocol):
    if protocol == "four" and type(document) is list:
        rows = []
        for row in document[:-1]:
            if type(row) is list and len(row) == 4:
                s, u, t, m = row
                row = [s, u, t, 0 if type(m) is list and not m else m]
            rows.append(row)
        document = rows + document[-1:]
    return shift(document)


def source_rewrites():
    provenance = json.loads((ROOT / "PROVENANCE.json").read_text())
    for entry in provenance["controls"]:
        raw = (ROOT / entry["local"]).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw)
        if (blob.hexdigest() != entry["git_blob_sha1"] or
                hashlib.sha256(raw).hexdigest() != entry["sha256"]):
            raise ValueError(f"Control hash mismatch: {entry['local']}")

    def shifted(source):
        return (source.replace("d=0", "d=2").replace("d=3", "d=5")
                .replace("r, 3)", "r, 5)")
                .replace("r[:3], 3)", "r[:3], 5)")
                .replace("t, 2)", "t, 4)"))

    for old, new in [("entry_tokens304", "strict_tokens299"),
                     ("ast340", "strict_ast335")]:
        source = (ROOT / "controls" / (old + ".py")).read_text()
        changed = source.replace("(d % 2 or not k) and i(t, d=3)",
                                 "d % 2 * i(t, d=3)")
        changed = changed.replace("b'\\x00'", "b'\\x01'")
        if old == "ast340":
            changed = changed.replace("i = lambda a, t=0j, d=(k := 0):",
                                      "k = 0\ni = lambda a, t=0j, d=0:")
        changed = shifted(changed)
        actual = (ROOT / "checkers" / (new + ".py")).read_text()
        if ast.dump(ast.parse(changed)) != ast.dump(ast.parse(actual)):
            raise ValueError(f"Unexpected source change in {new}")
    old = (ROOT / "controls/bytes584.py").read_text()
    changed = shifted(old).replace("c([[]], q())", "c([1], q())")
    actual = (ROOT / "checkers/strict_bytes583.py").read_text()
    if ast.dump(ast.parse(changed)) != ast.dump(ast.parse(actual)):
        raise ValueError("Unexpected source change in byte profile")


def run(job):
    profile, protocol, case, path, candidate, optimized = job
    document = target(case["certificate"], protocol) if candidate else case["certificate"]
    try:
        process = subprocess.run(
            [sys.executable, *(["-O"] if optimized else []), str(ROOT / path)],
            input=json.dumps(document), text=True, capture_output=True,
            timeout=20)
        accepted = process.returncode == 0 and process.stdout == "ACCEPT\n"
        error = None if accepted else (process.stderr.splitlines()[-1]
                                       if process.stderr else "no acceptance")
    except subprocess.TimeoutExpired:
        accepted, error = False, "resource timeout (not acceptance)"
    return {"profile": profile, "case": case["name"], "path": path,
            "optimized": optimized, "expected": case["expected"],
            "accepted": accepted, "error": error}


def main():
    source_rewrites()
    measurements = [measure(path) for path in EXPECTED]
    fixtures = {p: json.loads((ROOT / "fixtures" / (p + "_cases.json"))
                             .read_text())["cases"] for p in ["three", "four"]}
    profiles = [
        ("tokens", "three", "controls/entry_tokens304.py", "checkers/strict_tokens299.py"),
        ("ast", "three", "controls/ast340.py", "checkers/strict_ast335.py"),
        ("bytes", "four", "controls/bytes584.py", "checkers/strict_bytes583.py"),
    ]
    jobs = [(profile, protocol, case, path, candidate, optimized)
            for profile, protocol, control, candidate_path in profiles
            for case in fixtures[protocol]
            for path, candidate in [(control, False), (candidate_path, True)]
            for optimized in (False, True)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(run, jobs))
    failures = [r for r in results if r["expected"] != r["accepted"]]
    metrics = {"python": sys.version, "normalization": "ast.unparse(tree) + LF",
               "files": measurements, "candidate_envelope": [299, 335, 583],
               "matched_entry_control_envelope": [304, 340, 584],
               "current_repository_strict_envelope": [302, 340, 584],
               "current_repository_compact_cross_contract_extrema": [239, 255, 460],
               "qualification": "Different programs; shifted public encoding; no global minimum claim."}
    (ROOT / "measurements.json").write_text(json.dumps(metrics, indent=2) + "\n")
    receipt = {"python": sys.version, "source_rewrites_verified": True,
               "cases": {p: len(c) for p, c in fixtures.items()},
               "executions": len(results), "failures": failures,
               "scope": "Finite regression evidence, not formal verification.",
               "results": results}
    (ROOT / "validation.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"executions": len(results), "failures": failures,
                      "candidate_envelope": [299, 335, 583]}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
