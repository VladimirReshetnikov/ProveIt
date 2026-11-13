"""Standalone differential CLI audit of the composed 476-byte checker.

The 40 unique upstream fixture bytes are stored by their Git blob SHA.
The 66 original labels and inherited expectations are retained. Finite
checks supplement the written proof; they do not prove completeness.
"""
import ast
import concurrent.futures
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
index = json.loads((ROOT / "fixture_index.json").read_text())
cases = json.loads((ROOT / "cases.json").read_text())
by_name = {Path(row["path"]).name: row for row in index}


def measure(path):
    tree = ast.parse(path.read_text())
    text = ast.unparse(tree) + "\n"
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
               tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}
    return {"tokens": sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(text).readline)),
            "ast_nodes": sum(1 for _ in ast.walk(tree)),
            "normalized_bytes": len(text.encode()),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def check(case):
    row = by_name[case["file"]]
    payload = (ROOT / "fixtures" / (row["sha"] + ".json")).read_bytes()
    blob_sha = hashlib.sha1(b"blob " + str(len(payload)).encode() + b"\0" + payload).hexdigest()
    if blob_sha != row["sha"]:
        raise ValueError("Upstream fixture hash mismatch: " + case["file"])
    results = []
    for name in ("control477.py", "checker476.py"):
        for optimized in (False, True):
            command = [sys.executable, "-I", "-S", "-B"]
            if optimized:
                command.append("-O")
            command.append(str(ROOT / name))
            try:
                p = subprocess.run(command, input=payload, capture_output=True, timeout=10)
                accepted = p.returncode == 0 and p.stdout == b"ACCEPT\n"
                results.append({"program": name, "optimized": optimized,
                                "accepted": accepted,
                                "expected": case["candidate_expected"],
                                "passed": accepted == case["candidate_expected"],
                                "returncode": p.returncode})
            except subprocess.TimeoutExpired:
                results.append({"program": name, "optimized": optimized,
                                "accepted": False, "expected": case["candidate_expected"],
                                "passed": False, "timeout": True})
    return {"fixture": case["file"], "blob_sha": row["sha"],
            "upstream_expected": case["candidate_expected"], "results": results}


if __name__ == "__main__":
    control = (ROOT / "control477.py").read_text()
    candidate = (ROOT / "checker476.py").read_text()
    if control.count("bool(m or 3 % len(a))") != 1:
        raise ValueError("Control rewrite site is not unique")
    if candidate != control.replace("bool(m or 3 % len(a))", "any((m, 3 % len(a)))"):
        raise ValueError("Candidate contains another source change")
    if any(s != ast.unparse(ast.parse(s)) + "\n" for s in (control, candidate)):
        raise ValueError("Checker sources are not normalized")
    payload = control.encode()
    control_blob_sha = hashlib.sha1(b"blob " + str(len(payload)).encode() + b"\0" + payload).hexdigest()
    if control_blob_sha != "48cc9c417ea9e011edf5f1c5fafd91f33a205fbf":
        raise ValueError("Control does not match upstream Git blob")
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(check, cases))
    failures = [r for r in results if any(not x["passed"] for x in r["results"])]
    discrepancies = [r for r in results if len({x["accepted"] for x in r["results"]}) > 1]
    report = {"python": sys.version, "upstream_commit": "6874c85a4cea45d881de73620284fcc75d740942",
              "exact_single_rewrite": True, "normalized_sources": True,
              "control_git_blob_sha": control_blob_sha,
              "metrics": {name: measure(ROOT / name) for name in ("control477.py", "checker476.py")},
              "labelled_fixtures": len(cases), "unique_fixture_blobs": len({r["blob_sha"] for r in results}),
              "expected_accept_labels": sum(c["candidate_expected"] for c in cases),
              "process_executions": len(cases) * 4,
              "failures": failures, "discrepancies": discrepancies, "results": results}
    (ROOT / "fixture_audit.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "results"}, indent=2))
    if failures or discrepancies:
        raise SystemExit(1)
