"""Self-contained measurements and meaningful proof/scope regression checks."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
PROGRAMS = ("checker_without_injectivity.py", "checker_with_injectivity.py")
ignored = {tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
           tokenize.DEDENT, tokenize.ENDMARKER, tokenize.ENCODING}
metrics = []
for name in PROGRAMS:
    raw = (ROOT / name).read_bytes()
    normalized = (ast.unparse(ast.parse(raw)) + "\n").encode()
    compressed = gzip.compress(normalized, compresslevel=9, mtime=0)
    (ROOT / (name + ".gz")).write_bytes(compressed)
    metrics.append({"file": name, "raw_bytes": len(raw),
                    "significant_tokens": sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
                    "ast_nodes": len(list(ast.walk(ast.parse(normalized)))),
                    "normalized_bytes": len(normalized), "gzip9_bytes": len(compressed),
                    "source_sha256": hashlib.sha256(raw).hexdigest(),
                    "normalized_sha256": hashlib.sha256(normalized).hexdigest()})

small = (ROOT / PROGRAMS[0]).read_text()
large = (ROOT / PROGRAMS[1]).read_text()
branch = '''    if name == "injectivity":
        left, right = parts
        term(left, parameters)
        term(right, parameters)
        return ["imp", ["=", ["S", left], ["S", right]], ["=", left, right]]
'''
if large.replace(branch, "") != small or large.count(branch) != 1:
    raise RuntimeError("The matched controls differ beyond one axiom branch")
rows = []
for case in json.loads((ROOT / "fixtures/index.json").read_text()):
    payload = (ROOT / "fixtures" / (case["name"] + ".json")).read_bytes()
    for program in PROGRAMS:
        expected = case["expected_without" if program == PROGRAMS[0] else "expected_with"]
        for optimized in (False, True):
            command = [sys.executable, "-I", "-S", "-B"] + (["-O"] if optimized else []) + [str(ROOT / program)]
            result = subprocess.run(command, input=payload, capture_output=True, timeout=10)
            accepted = result.returncode == 0 and result.stdout == b"ACCEPT\n"
            rows.append({"fixture": case["name"], "program": program, "optimized": optimized,
                         "expected": expected, "accepted": accepted,
                         "last_error": result.stderr.decode(errors="replace").splitlines()[-1] if result.stderr else ""})
failures = [r for r in rows if r["expected"] != r["accepted"]]
report = {"python": sys.version, "exact_single_branch_difference": True,
          "metrics": metrics, "executions": len(rows), "unexpected_outcomes": len(failures),
          "results": rows, "failures": failures}
(ROOT / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"metrics": metrics, "executions": len(rows), "unexpected_outcomes": len(failures)}, indent=2))
if failures:
    print(json.dumps(failures, indent=2))
    raise SystemExit(1)
