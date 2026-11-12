"""Measure and compare the native public-goal validating profiles."""
from pathlib import Path
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    source = ast.unparse(tree) + "\n"
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
               tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT}
    return {"file": path.name,
            "tokens": sum(t.type not in ignored for t in
                          tokenize.generate_tokens(io.StringIO(source).readline)),
            "ast": sum(1 for _ in ast.walk(tree)),
            "bytes": len(source.encode()),
            "git_blob_sha1": hashlib.sha1(
                f"blob {len(raw)}\0".encode() + raw).hexdigest(),
            "sha256": hashlib.sha256(raw).hexdigest()}


metrics = [measure(ROOT / name) for name in
           ("control641.py", "control643.py", "checker.py")]
assert metrics[0]["git_blob_sha1"] == "fc91b7f20c111e56d9dfd2ab9d3c354d5ad32e51"
assert metrics[1]["git_blob_sha1"] == "3bc3d7bb66da371af195f7b092ad6a078eff70fd"
assert [(m["tokens"], m["ast"], m["bytes"]) for m in metrics] == [
    (325, 375, 641), (327, 375, 643), (324, 374, 629)]

cases = json.loads((ROOT / "fixtures/cases.json").read_text())
checks = []
for case in cases:
    payload = (ROOT / "fixtures" / case["file"]).read_bytes()
    for optimized in (False, True):
        outcomes = []
        for name in ("control641.py", "checker.py"):
            command = [sys.executable, "-I", "-S", "-B"]
            if optimized:
                command.append("-O")
            command.append(str(ROOT / name))
            result = subprocess.run(command, input=payload, capture_output=True,
                                    timeout=30)
            accepted = result.returncode == 0 and result.stdout == b"ACCEPT\n"
            outcomes.append(accepted)
            checks.append({"case": case["file"], "checker": name,
                           "optimized": optimized, "accepted": accepted,
                           "expected": case["expected"],
                           "passed": accepted == case["expected"]})
        assert outcomes[0] == outcomes[1]

report = {"python": sys.version, "metrics": metrics,
          "checks": checks, "cli_checks": len(checks),
          "failures": sum(not c["passed"] for c in checks),
          "limits": [
              "The public closed native Eq/D goal is checked in the measured module.",
              "This is not the stronger whole-certificate alphabet-validation contract.",
              "Unused non-integer/list JSON prefixes are permitted, as in the matched controls.",
              "Universal soundness and completeness are conditional on the inherited finite integer/list certificate theorem and context-first scheduling audit.",
              "No equality of all malformed JSON success languages is claimed.",
              "No arithmetic or logical axiom changes; no global minimum is proved."]}
(ROOT / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({key: report[key] for key in
                 ("metrics", "cli_checks", "failures")}, indent=2))
if report["failures"]:
    raise SystemExit(1)
