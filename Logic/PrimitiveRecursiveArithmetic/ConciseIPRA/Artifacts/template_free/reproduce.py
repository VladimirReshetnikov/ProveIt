#!/usr/bin/env python3
"""Reproduce certificate checks, source provenance, and whole-program metrics."""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence"
SKIP = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
    tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}


def metrics(path):
    source = (ast.unparse(ast.parse(path.read_text())) + "\n").encode()
    return {
        "normalized_bytes": len(source),
        "significant_tokens": sum(
            token.type not in SKIP
            for token in tokenize.tokenize(io.BytesIO(source).readline)
        ),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(source))),
        "gzip9_normalized_bytes": len(
            gzip.compress(source, compresslevel=9, mtime=0)
        ),
        "normalized_sha256": hashlib.sha256(source).hexdigest(),
    }


def main():
    verified = []
    for manifest in ("sources.json", "comparison_sources.json"):
        record = json.loads((EVIDENCE / manifest).read_text())
        for item in record["files"]:
            path = ROOT / item["local_file"]
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            if digest != item["sha256"]:
                raise SystemExit("Source hash mismatch: " + item["local_file"])
            verified.append(item["local_file"])
    print("Verified", len(verified), "pinned source files.")

    for script in ("tests/verify_strict.py", "compact/verify.py"):
        result = subprocess.run(
            [sys.executable, str(ROOT / script)], cwd=ROOT, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT
        )
        if result.returncode:
            print(result.stdout)
            raise SystemExit(result.returncode)
        print(script + ": PASS")

    comparison = json.loads((EVIDENCE / "comparison_sources.json").read_text())
    baseline_rows = []
    for item in comparison["files"]:
        if "remeasured" in item:
            observed = metrics(ROOT / item["local_file"])
            baseline_rows.append({
                "path": item["local_file"],
                "observed": observed,
                "matches_recorded_environment": observed == item["remeasured"],
            })
    strict = json.loads((EVIDENCE / "strict_validation.json").read_text())
    compact = json.loads((ROOT / "compact/results.json").read_text())
    strict_ok = not strict["failures"]
    compact_ok = compact["passed"]
    report = {
        "python": sys.version,
        "implementation": platform.python_implementation(),
        "zlib_runtime": zlib.ZLIB_RUNTIME_VERSION,
        "pinned_source_hashes_verified": len(verified),
        "strict_process_runs": strict["process_runs"],
        "strict_process_failures": len(strict["failures"]),
        "strict_traversal_checks": strict["traversal_comparisons"],
        "compact_global_process_runs": len(compact["expectations"]),
        "compact_mutant_controls": len(compact["mutation_controls"]),
        "compact_forward_control": compact["forward_x_control"],
        "comparison_measurements": baseline_rows,
        "all_certificate_expectations_passed": strict_ok and compact_ok,
        "limits": (
            "Finite checks do not prove universal soundness. "
            "Normalization and gzip metrics can vary across runtime versions."
        ),
    }
    (EVIDENCE / "reproduction.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    changed = [x["path"] for x in baseline_rows if not x["matches_recorded_environment"]]
    if changed:
        print("Runtime-dependent measurement differences:", ", ".join(changed))
    print("Strict processes:", strict["process_runs"], "with", len(strict["failures"]), "failures")
    print("Compact processes:", len(compact["expectations"]), "plus controls: PASS")
    print("Reproduction receipt: evidence/reproduction.json")
    if not strict_ok or not compact_ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
