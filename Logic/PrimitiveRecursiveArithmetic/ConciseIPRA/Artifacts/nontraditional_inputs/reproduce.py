"""Verify delivered integrity, remeasure complete programs, optionally replay tests."""
from pathlib import Path
import argparse
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
           tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
PROGRAMS = {
    "sequent_input/checker_sequent458.py": (265, 297, 458),
    "sequent_input/baseline/code/checker_bytes460.py": (266, 299, 460),
    "expression_input/code/checker_tokens299.py": (299, 350, 632),
    "expression_input/code/checker_ast338.py": (311, 338, 667),
    "expression_input/code/checker_bytes575.py": (308, 358, 575),
}


def measure(path):
    tree = ast.parse(path.read_text())
    normalized = ast.unparse(tree) + "\n"
    return (sum(t.type not in IGNORED for t in
                tokenize.generate_tokens(io.StringIO(normalized).readline)),
            sum(1 for _ in ast.walk(tree)), len(normalized.encode()))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tests", action="store_true")
    args = parser.parse_args()
    manifest = ROOT / "MANIFEST.sha256"
    if not manifest.exists():
        raise SystemExit("Missing delivered MANIFEST.sha256")
    count = 0
    for line in manifest.read_text().splitlines():
        expected, name = line.split("  ", 1)
        path = ROOT / name
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise SystemExit("Integrity mismatch: " + name)
        count += 1
    print(f"Integrity verified: {count} files")
    measured = {name: measure(ROOT / name) for name in PROGRAMS}
    print(json.dumps({"python": sys.version, "measurements": measured}, indent=2))
    if sys.version_info[:3] == (3, 12, 14) and measured != PROGRAMS:
        raise SystemExit("Published metrics differ")
    if args.tests:
        for subdir, script in (("sequent_input", "verify_sequents.py"),
                               ("expression_input", "verify.py")):
            subprocess.run([sys.executable, script], cwd=ROOT / subdir, check=True)
    print("Requested verification completed.")


if __name__ == "__main__":
    main()
