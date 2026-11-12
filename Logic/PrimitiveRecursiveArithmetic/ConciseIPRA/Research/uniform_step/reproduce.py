"""Reproduce verification, measurements, and optionally the PDF."""
import argparse
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence"


def normalized_source(path):
    tree = ast.parse(path.read_text())
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and isinstance(node.body[0].value.value, str)):
                node.body.pop(0)
    return tree, (ast.unparse(tree) + "\n").encode()


def measure(path):
    tree, data = normalized_source(path)
    ignored = {tokenize.COMMENT, tokenize.ENCODING, tokenize.ENDMARKER,
               tokenize.INDENT, tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL}
    tokens = sum(t.type not in ignored for t in
                 tokenize.generate_tokens(io.StringIO(data.decode()).readline))
    return {"normalized_bytes": len(data), "tokens": tokens,
            "ast_nodes": sum(1 for _ in ast.walk(tree)),
            "gzip9_bytes": len(gzip.compress(data, compresslevel=9, mtime=0)),
            "source_bytes": path.stat().st_size,
            "source_gzip9_bytes": len(gzip.compress(path.read_bytes(), compresslevel=9, mtime=0)),
            "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "normalized_sha256": hashlib.sha256(data).hexdigest()}


def run(relative):
    result = subprocess.run([sys.executable, str(ROOT / relative)],
                            cwd=ROOT, capture_output=True, text=True)
    name = relative.replace("/", "_") + ".log"
    (EVIDENCE / name).write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f"{relative} failed; see evidence/{name}")
    print(f"PASS: {relative}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pdf", action="store_true")
    args = parser.parse_args()
    EVIDENCE.mkdir(exist_ok=True)
    run("code/verify.py")
    run("code/native/test_step.py")
    run("code/review.py")
    for source, target in [
        ("code/clausal_verification.json", "clausal_verification.json"),
        ("code/clausal_review.json", "clausal_review.json"),
        ("code/native/test_results.json", "native_verification.json"),
    ]:
        shutil.copy2(ROOT / source, EVIDENCE / target)
    paths = ["code/checker.py", "code/control_zero.py", "code/control_raw.py",
             "code/reference/incoming_clausal.py", "code/reference/current_eval.py",
             "code/native/zero_normal_control.py", "code/native/successor_eval.py"]
    measurements = {name: measure(ROOT / name) for name in paths}
    (EVIDENCE / "metrics.json").write_text(
        json.dumps({"python": sys.version, "programs": measurements}, indent=2) + "\n")
    normalized = ROOT / "code/normalized"
    normalized.mkdir(exist_ok=True)
    for name in paths[:3]:
        _, data = normalized_source(ROOT / name)
        stem = Path(name).name
        (normalized / stem).write_bytes(data)
        (normalized / (stem + ".gz")).write_bytes(gzip.compress(data, compresslevel=9, mtime=0))
        (normalized / (stem + ".raw.gz")).write_bytes(
            gzip.compress((ROOT / name).read_bytes(), compresslevel=9, mtime=0))
    provenance = json.loads((EVIDENCE / "provenance.json").read_text())
    for entry in provenance["inherited_mathematics"]:
        data = (ROOT / "reference" / Path(entry["path"]).name).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if blob != entry["pinned_blob"]:
            raise RuntimeError("Inherited source no longer matches pinned Git blob")
    print("PASS: inherited source authentication")
    if args.pdf:
        subprocess.run([sys.executable, str(ROOT / "build_report.py"), "--pdf"], check=True)
    print(json.dumps({"checker": measurements["code/checker.py"],
                      "all_validation_suites": "passed"}, indent=2))


if __name__ == "__main__":
    main()
