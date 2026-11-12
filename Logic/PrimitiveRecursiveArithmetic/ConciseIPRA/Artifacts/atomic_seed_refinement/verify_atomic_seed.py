"""Recheck all certificates in normal and optimized Python; report full metrics."""
from pathlib import Path
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent


def metrics(path):
    source = path.read_text()
    tree = ast.parse(source)
    normalized = ast.unparse(tree) + "\n"
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = [token for token in tokenize.generate_tokens(io.StringIO(normalized).readline)
              if token.type not in ignored]
    return {"path": path.name, "significant_tokens": len(tokens),
            "ast_nodes": sum(1 for _ in ast.walk(tree)),
            "normalized_utf8_bytes": len(normalized.encode()),
            "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
            "normalized_sha256": hashlib.sha256(normalized.encode()).hexdigest()}


def run(program, payload, optimized):
    command = [sys.executable, "-I", "-S", "-B"]
    if optimized:
        command.append("-O")
    command.append(str(program))
    process = subprocess.run(command, input=payload, capture_output=True, timeout=20)
    return process.returncode == 0 and process.stdout == b"ACCEPT\n"


def main():
    cases = json.loads((ROOT / "tests/atomic_cases.json").read_text())
    rows = []
    for case in cases:
        payload = (ROOT / "tests" / case["file"]).read_bytes()
        for optimized in (False, True):
            accepted = run(ROOT / "code/atomic_seed_checker.py", payload, optimized)
            rows.append(dict(case, optimized=optimized, actual=accepted,
                             passed=accepted == case["accepted"]))
    malformed = [
        ("nonobject", b"[]"),
        ("extra_field", b'{"goal":["=",["z"],["z"]],"proof":["hyp",0],"extra":0}'),
        ("boolean_variable", b'{"goal":["d",["=",["v",true],["v",true]]],"proof":["hyp",0]}'),
        ("unknown_term", b'{"goal":["=",["unknown"],["z"]],"proof":["hyp",0]}'),
        ("unknown_formula", b'{"goal":["unknown"],"proof":["hyp",0]}'),
    ]
    for name, payload in malformed:
        for optimized in (False, True):
            accepted = run(ROOT / "code/atomic_seed_checker.py", payload, optimized)
            rows.append({"file": name, "accepted": False, "optimized": optimized,
                         "actual": accepted, "passed": not accepted})
    controls = []
    control = ROOT / "reference/atomic_raw_control.py"
    if control.exists():
        z, one, body = ["z"], ["s", ["z"]], ["s", ["v", 0]]
        payload = json.dumps({"goal": ["=", ["i", z, one, body], one],
                              "proof": ["zero", one, body]}).encode()
        for optimized in (False, True):
            accepted = run(control, payload, optimized)
            controls.append({"case": "primitive_zero", "optimized": optimized,
                             "actual": accepted, "passed": accepted})
            payload_new = (ROOT / "tests/certificates/zero_compound_seed.json").read_bytes()
            accepted_new = run(control, payload_new, optimized)
            controls.append({"case": "new_raw_qe_certificate", "optimized": optimized,
                             "actual": accepted_new, "passed": not accepted_new})
    result = {"python": sys.version, "candidate_cases": rows,
              "control_cases": controls,
              "metrics": [metrics(ROOT / "code/atomic_seed_checker.py")] +
                         ([metrics(control)] if control.exists() else []),
              "failures": sum(not row["passed"] for row in rows + controls)}
    (ROOT / "evidence/atomic_verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"checker_executions": len(rows) + len(controls),
                      "failures": result["failures"], "metrics": result["metrics"]}, indent=2))
    if result["failures"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
