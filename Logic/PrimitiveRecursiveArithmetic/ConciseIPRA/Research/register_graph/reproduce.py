"""Reproduce the delivered tests and complete-source measurements.

This is an untrusted reproduction driver, not part of a proof checker.
"""
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
EVIDENCE = ROOT / "evidence"
EVIDENCE.mkdir(exist_ok=True)


def run(relative, receipt):
    process = subprocess.run([sys.executable, str(ROOT / relative)],
                             cwd=ROOT, text=True, capture_output=True,
                             timeout=600)
    if process.returncode:
        raise RuntimeError(relative + " failed:\n" + process.stdout + process.stderr)
    if receipt:
        try:
            result = json.loads(process.stdout)
        except json.JSONDecodeError:
            result = {"stdout": process.stdout, "stderr": process.stderr,
                      "returncode": process.returncode}
        (EVIDENCE / receipt).write_text(json.dumps(result, indent=2) + "\n")
    print(relative + ": passed")


def measure(relative):
    path = ROOT / relative
    raw = path.read_bytes()
    normalized = (ast.unparse(ast.parse(raw.decode("utf-8"))) + "\n").encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
               tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}
    tokens = sum(token.type not in ignored
                 for token in tokenize.tokenize(io.BytesIO(normalized).readline))
    return {
        "path": relative,
        "raw_bytes": len(raw),
        "normalized_bytes": len(normalized),
        "significant_tokens": tokens,
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
        "gzip9_raw_bytes": len(gzip.compress(raw, compresslevel=9, mtime=0)),
        "gzip9_normalized_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        "sha256_raw": hashlib.sha256(raw).hexdigest(),
        "sha256_normalized": hashlib.sha256(normalized).hexdigest(),
    }


def main():
    for relative, receipt in [
        ("code/register_iterator.py", "semantic_checks.json"),
        ("code/counter_register_iterator.py", "counter_semantic_checks.json"),
        ("code/pr_to_register_ast.py", "ast_compiler_checks.json"),
        ("code/test_checker.py", "j_checker_driver_output.json"),
        ("ancillary/reproduce_288.py", "ancillary_driver_output.json"),
    ]:
        run(relative, receipt)
    for source, destination in [
        (ROOT / "code/validation.json", EVIDENCE / "j_checker_validation.json"),
        (ROOT / "code/metrics.json", EVIDENCE / "j_checker_metrics.json"),
    ]:
        if source.exists():
            destination.write_bytes(source.read_bytes())
    paths = ["reference/old_byte_leader.py", "reference/old_ast_leader.py",
             "ancillary/reference/code/checker_structure.py",
             "ancillary/checker_288.py", "code/checker.py"]
    result = {"python": sys.version, "normalization": "ast.unparse plus one newline",
              "gzip_role": "informational only", "checkers": [measure(p) for p in paths]}
    (EVIDENCE / "complete_checker_metrics.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
