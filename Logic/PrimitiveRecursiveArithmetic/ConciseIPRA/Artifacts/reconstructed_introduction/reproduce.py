"""Verify the delivered manifest, remeasure all selected programs, and test."""
import argparse
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
PROFILES = ["exact/code/checker.py", "sorted/code/checker.py",
            "synthesis/synthesis_checker.py"]
EXPECTED = {
    "exact/code/checker.py": (313, 357, 590, 370),
    "sorted/code/checker.py": (298, 336, 573, 358),
    "synthesis/synthesis_checker.py": (1896, 2182, 7639, 2249),
}


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    normalized = (ast.unparse(tree) + "\n").encode()
    return {
        "path": str(path.relative_to(ROOT)),
        "tokens": sum(t.type not in SKIP for t in
                      tokenize.tokenize(io.BytesIO(normalized).readline)),
        "ast_nodes": len(list(ast.walk(ast.parse(normalized)))),
        "normalized_bytes": len(normalized),
        "gzip9_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        "raw_sha256": hashlib.sha256(raw).hexdigest(),
        "normalized_sha256": hashlib.sha256(normalized).hexdigest(),
    }


def verify_manifest():
    manifest = ROOT / "MANIFEST.sha256"
    if not manifest.is_file():
        raise ValueError("The delivery manifest is missing.")
    checked = 0
    for line in manifest.read_text().splitlines():
        expected, name = line.split("  ", 1)
        actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError("Manifest mismatch: " + name)
        checked += 1
    return checked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tests", action="store_true")
    args = parser.parse_args()
    manifest_count = verify_manifest()
    paths = [ROOT / name for name in PROFILES]
    paths += sorted((ROOT / "reference/controls").glob("*.py"))
    rows = [measure(path) for path in paths]
    for row in rows[:3]:
        actual = tuple(row[k] for k in
                       ("tokens", "ast_nodes", "normalized_bytes", "gzip9_bytes"))
        if actual != EXPECTED[row["path"]]:
            raise ValueError("Measurement mismatch; use CPython 3.12.14: " + str(row))
    tests = []
    if args.tests:
        for name in ["exact/tests/verify.py", "sorted/tests/verify.py",
                     "synthesis/verify_synthesis.py"]:
            result = subprocess.run([sys.executable, str(ROOT / name)], cwd=ROOT,
                                    capture_output=True, text=True)
            tests.append({"script": name, "exit_code": result.returncode,
                          "output": result.stdout.strip()})
            if result.returncode:
                print(result.stderr)
                print(result.stdout)
                raise SystemExit(result.returncode)
    report = {"python": sys.version, "zlib": zlib.ZLIB_VERSION,
              "manifest_files": manifest_count, "measurements": rows,
              "tests": tests}
    destination = ROOT / "reproduced"
    destination.mkdir(exist_ok=True)
    (destination / "receipt.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"manifest_files": manifest_count,
                      "measurements": rows[:3],
                      "test_suites_passed": len(tests)}, indent=2))


if __name__ == "__main__":
    main()
