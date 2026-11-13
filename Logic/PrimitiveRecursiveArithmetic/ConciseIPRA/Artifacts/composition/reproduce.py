"""Reproduce the delivered checks and complete-module measurements offline."""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def main():
    for script in ["code/build_examples.py", "code/verify_pointfree.py",
                   "code/verify_environment.py", "compact_refinement/verify.py"]:
        subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT, check=True)
    measurements = []
    paths = [ROOT / "code" / "pointfree_checker.py"]
    paths += sorted((ROOT / "compact_refinement" / "code").glob("*.py"))
    for p in paths:
        tree = ast.parse(p.read_text())
        data = (ast.unparse(tree) + "\n").encode()
        measurements.append(dict(
            path=str(p.relative_to(ROOT)),
            tokens=sum(t.type not in SKIP for t in tokenize.tokenize(io.BytesIO(data).readline)),
            ast_nodes=sum(1 for _ in ast.walk(tree)),
            normalized_bytes=len(data),
            gzip9_bytes=len(gzip.compress(data, compresslevel=9, mtime=0))))
    expected = json.loads((ROOT / "evidence" / "measurements.json").read_text())
    if measurements != expected:
        raise RuntimeError({"reason": "measurements differ; compare Python versions",
                            "actual": measurements, "recorded": expected})
    ledger = json.loads((ROOT / "reference" / "source_census.json").read_text())
    historical_hashes = {r["normalized_sha256"] for r in ledger["entries"]}
    duplicates = {}
    for p in sorted((ROOT / "compact_refinement" / "code").glob("checker_*.py")):
        data = (ast.unparse(ast.parse(p.read_text())) + "\n").encode()
        duplicates[p.name] = hashlib.sha256(data).hexdigest() in historical_hashes
    if any(duplicates.values()):
        raise RuntimeError("a new module duplicates a normalized census hash")
    receipt = dict(status="passed", python=sys.version,
                   measurements=measurements, historical_entries=len(ledger["entries"]),
                   normalized_hash_matches=duplicates)
    (ROOT / "evidence" / "reproduction.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
