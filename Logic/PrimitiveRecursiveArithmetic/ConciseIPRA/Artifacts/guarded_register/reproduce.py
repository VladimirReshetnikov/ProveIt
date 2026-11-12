"""Offline reproduction for the complete guarded-J research package."""

import argparse
import ast
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
EXCLUDED = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
    tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read_json(path):
    return json.loads((ROOT / path).read_text(encoding="utf-8"))


def measure(source):
    tree = ast.parse(source)
    normalized = ast.unparse(tree) + "\n"
    tokens = tokenize.generate_tokens(io.StringIO(normalized).readline)
    return {
        "tokens": sum(t.type not in EXCLUDED for t in tokens),
        "ast_nodes": sum(1 for _ in ast.walk(tree)),
        "normalized_bytes": len(normalized.encode("utf-8")),
    }


def blob_hash(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def verify_manifest():
    manifest = read_json("MANIFEST.json")
    for relative, expected in manifest["files"].items():
        path = ROOT / relative
        require(path.is_file(), "Missing delivered file: " + relative)
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        require(actual == expected, "Delivered file changed: " + relative)
    print("Verified SHA-256 manifest:", len(manifest["files"]), "files", flush=True)


def verify_reference_sources():
    provenance = read_json("evidence/provenance.json")
    for record in provenance["baseline_sources"]:
        data = (ROOT / record["local_file"]).read_bytes()
        require(hashlib.sha256(data).hexdigest() == record["sha256"],
                "Comparator SHA-256 mismatch: " + record["local_file"])
        require(blob_hash(data) == record["git_blob_sha"],
                "Comparator Git blob mismatch: " + record["local_file"])
    corpus = read_json("evidence/source_corpus.json")
    recorded = {r["sha"]: r for r in read_json("evidence/corpus_metrics.json")}
    require(len(corpus) == len(recorded) == 442, "Unexpected source corpus size")
    for record in corpus:
        data = record["content"].encode("utf-8")
        require(len(data) == record["size"] and blob_hash(data) == record["sha"],
                "Corpus Git blob mismatch: " + record["sha"])
        actual = measure(record["content"])
        expected = {key: recorded[record["sha"]][key] for key in actual}
        require(actual == expected, "Corpus metrics mismatch: " + record["sha"])
    print("Verified all 442 retrieved blobs and their recorded metrics", flush=True)


def verify_comparison():
    expected = {
        "reference/baseline_tokens.py": (256, 283, 594),
        "reference/baseline_ast.py": (263, 276, 580),
        "reference/baseline_bytes.py": (267, 303, 506),
        "code/checker_i.py": (1045, 1193, 3566),
        "code/checker_j.py": (1041, 1181, 3467),
    }
    for relative, values in expected.items():
        result = measure((ROOT / relative).read_text(encoding="utf-8"))
        require(tuple(result.values()) == values,
                "Metrics mismatch for " + relative + "; expected CPython 3.12.14")
        print(relative, result, flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", action="store_true",
                        help="first verify SHA-256 hashes of delivered files")
    parser.add_argument("--pdf", action="store_true",
                        help="also build report.pdf with latexmk")
    args = parser.parse_args()
    print("Runtime:", platform.python_implementation(), platform.python_version(), flush=True)
    if args.manifest:
        verify_manifest()
    verify_reference_sources()
    verify_comparison()
    subprocess.run([sys.executable, "reproduce.py"], cwd=ROOT / "code", check=True)
    subprocess.run([sys.executable, "symbolic.py"], cwd=ROOT / "code", check=True)
    evidence = read_json("code/evidence.json")
    actual = tuple(evidence[key] for key in ["test_runs", "accepted", "rejected", "mismatches"])
    require(actual == (108, 48, 60, 0), "Unexpected subprocess test results")
    symbolic = read_json("code/symbolic_evidence.json")
    require(symbolic["checks"] == 12 and symbolic["failures"] == 0,
            "Unexpected symbolic proof results")
    if args.pdf:
        subprocess.run(["latexmk", "-pdf", "-interaction=nonstopmode",
                        "-halt-on-error", "report.tex"], cwd=ROOT, check=True)
    print("All offline measurements and proof checks reproduced successfully.", flush=True)
    print("The requested global compact-envelope improvement remains unmet.", flush=True)


if __name__ == "__main__":
    main()
