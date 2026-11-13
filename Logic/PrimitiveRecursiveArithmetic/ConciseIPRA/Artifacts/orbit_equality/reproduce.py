#!/usr/bin/env python3
"""Reproduce the delivered evidence in a temporary copy of this package."""
import ast
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
        tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def metrics(path):
    normalized = ast.unparse(ast.parse(path.read_text())) + "\n"
    return [sum(t.type not in SKIP for t in
                tokenize.generate_tokens(io.StringIO(normalized).readline)),
            len(list(ast.walk(ast.parse(normalized)))),
            len(normalized.encode("utf-8"))]


def check_manifest():
    manifest = ROOT / "MANIFEST.sha256"
    if not manifest.exists():
        return 0
    count = 0
    for line in manifest.read_text().splitlines():
        digest, name = line.split("  ", 1)
        path = ROOT / name
        require(path.is_file(), "Missing file: " + name)
        require(hashlib.sha256(path.read_bytes()).hexdigest() == digest,
                "Changed file: " + name)
        count += 1
    return count


def main():
    authenticated_files = check_manifest()
    profiles = {
        "checkers/whole_json_tokens.py": [248, 277, 615],
        "checkers/whole_json_ast.py": [254, 268, 613],
        "reference/whole_json_tokens249.py": [249, 278, 607],
        "reference/whole_json_ast269.py": [255, 269, 605],
        "reference/unchanged_byte473.py": [272, 308, 473],
    }
    measured = {name: metrics(ROOT / name) for name in profiles}
    for name, expected in profiles.items():
        require(measured[name] == expected,
                "Metric mismatch for " + name + "; exact normalization uses CPython 3.12.14")
    for name, other in [("tokens", "whole_json_tokens.py"),
                        ("ast", "whole_json_ast.py")]:
        require((ROOT / "checkers" / other).read_bytes() ==
                (ROOT / "whole_json_validation/candidate" / (name + "_whole.py")).read_bytes(),
                "Duplicated candidate files disagree")
    with tempfile.TemporaryDirectory(prefix="ipra_orbit_reproduce_") as directory:
        work = Path(directory) / "package"
        shutil.copytree(ROOT, work, ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        for script in ["code/equality_orbit.py", "whole_json_validation/verify.py",
                       "whole_json_validation/regenerate.py", "diagonal_certificate/run_checks.py"]:
            result = subprocess.run([sys.executable, "-B", str(work / script)],
                                    cwd=work, capture_output=True, text=True, timeout=180)
            require(result.returncode == 0,
                    script + " failed:\n" + result.stdout + result.stderr)
        arithmetic = json.loads((work / "code/equality_orbit_results.json").read_text())
        framing = json.loads((work / "whole_json_validation/verification.json").read_text())
        symbolic = json.loads((work / "diagonal_certificate/verification.json").read_text())
    summary = {
        "python": sys.version.split()[0],
        "manifest_files_verified": authenticated_files,
        "complete_checker_metrics_tokens_ast_bytes": measured,
        "raw_term_nodes": arithmetic["node_counts"],
        "raw_equality_pairs_evaluated": 25,
        "raw_predecessor_inputs_evaluated_each": 6,
        "numeric_orbit_pairs": 6400,
        "framing_fixture_files": framing["fixture_cases"],
        "framing_process_executions": framing["executions"],
        "framing_failures": len(framing["failures"]),
        "symbolic_certificate_receipt": symbolic,
        "scope": "Written universal proofs plus finite checks; no full iPRA proof-assistant formalization.",
    }
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
