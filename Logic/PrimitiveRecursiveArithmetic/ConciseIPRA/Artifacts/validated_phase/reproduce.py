"""Offline measurements and regression checks for the delivered checkers."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse
import ast
import gzip
import hashlib
import io
import json
import subprocess
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
           tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    tree = ast.parse(path.read_bytes())
    source = (ast.unparse(tree) + "\n").encode()
    return {"path": str(path.relative_to(ROOT)),
            "tokens": sum(t.type not in IGNORED for t in
                          tokenize.tokenize(io.BytesIO(source).readline)),
            "ast_nodes": sum(1 for _ in ast.walk(tree)),
            "normalized_bytes": len(source),
            "gzip9_bytes": len(gzip.compress(source, compresslevel=9, mtime=0)),
            "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "normalized_sha256": hashlib.sha256(source).hexdigest()}


def verify_manifest():
    manifest = ROOT / "MANIFEST.sha256"
    for line in manifest.read_text().splitlines():
        expected, name = line.split("  ", 1)
        actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError("Manifest mismatch: " + name)


def check(job):
    profile, case = job
    result = subprocess.run([sys.executable, str(ROOT / "code" / profile)],
                            input=json.dumps(case["certificate"]), text=True,
                            capture_output=True, timeout=15)
    accepted = result.returncode == 0 and result.stdout == "ACCEPT\n"
    return {"profile": profile, "case": case["name"],
            "expected": case["expected"], "accepted": accepted,
            "pass": accepted == case["expected"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--metrics-only", action="store_true")
    parser.add_argument("--verify-manifest", action="store_true")
    args = parser.parse_args()
    if args.verify_manifest:
        verify_manifest()
    profiles = ["checker_tokens300.py", "checker_ast337.py", "checker_bytes580.py"]
    rows = [measure(ROOT / "code" / name) for name in profiles]
    recorded = json.loads((ROOT / "evidence/measurements.json").read_text())["measurements"]
    for row in rows:
        original = next(r for r in recorded if r["path"] == row["path"])
        for field in ("tokens", "ast_nodes", "normalized_bytes", "source_sha256"):
            if row[field] != original[field]:
                raise ValueError("Measurement mismatch; use CPython 3.12.14: " + str(row))
    receipt = {"python": sys.version, "zlib": zlib.ZLIB_VERSION,
               "measurements": rows, "cases": []}
    if not args.metrics_only:
        three = json.loads((ROOT / "evidence/eager_three_traced_fixtures.json").read_text())
        three = three["cases"] if isinstance(three, dict) else three
        four = json.loads((ROOT / "validation/byte_cases.json").read_text())["cases"]
        jobs = [(p, case) for p in profiles[:2] for case in three]
        jobs += [(profiles[2], case) for case in four]
        with ThreadPoolExecutor(max_workers=4) as workers:
            receipt["cases"] = list(workers.map(check, jobs))
        failures = [r for r in receipt["cases"] if not r["pass"]]
        receipt["total_cases"] = len(receipt["cases"])
        receipt["failures"] = failures
        if failures:
            raise AssertionError(failures)
    destination = ROOT / "reproduced"
    destination.mkdir(exist_ok=True)
    (destination / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"measurements": rows,
                      "process_checks": len(receipt["cases"]),
                      "unexpected_results": 0}, indent=2))


if __name__ == "__main__":
    main()
