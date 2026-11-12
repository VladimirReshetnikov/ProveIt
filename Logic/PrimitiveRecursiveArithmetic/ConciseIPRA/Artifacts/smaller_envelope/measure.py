"""Measure complete modules using the pinned repository's source convention."""
import ast
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize


ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
           tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


class StripDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if node.body and isinstance(node.body[0], ast.Expr):
            value = node.body[0].value
            if isinstance(value, ast.Constant) and isinstance(value.value, str):
                node.body.pop(0)
        return node

    visit_Module = clean
    visit_FunctionDef = clean
    visit_AsyncFunctionDef = clean
    visit_ClassDef = clean


def measurement(path):
    raw = path.read_bytes()
    tree = StripDocstrings().visit(ast.parse(raw.decode("utf-8")))
    source = ast.unparse(tree) + "\n"
    tokens = sum(t.type not in IGNORED for t in
                 tokenize.generate_tokens(io.StringIO(source).readline))
    return {
        "path": str(path.relative_to(ROOT)),
        "tokens": tokens,
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(source))),
        "normalized_bytes": len(source.encode("utf-8")),
        "sha256": hashlib.sha256(raw).hexdigest(),
    }


def main():
    provenance = json.loads((ROOT / "PROVENANCE.json").read_text())
    for source in provenance["files"]:
        path = ROOT / source["local_path"]
        raw = path.read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw)
        if hashlib.sha256(raw).hexdigest() != source["sha256"]:
            raise ValueError("Frozen source SHA-256 mismatch: " + str(path))
        if blob.hexdigest() != source["git_blob_sha1"]:
            raise ValueError("Frozen source Git blob mismatch: " + str(path))
    paths = ["reference/checkers/tokens.py", "checkers/tokens.py",
             "reference/checkers/ast.py", "checkers/ast.py",
             "reference/checkers/bytes.py", "checkers/bytes.py",
             "checkers/readable_strict.py"]
    rows = [measurement(ROOT / path) for path in paths]
    result = {"python": platform.python_version(),
              "normalization": "Remove docstrings; ast.unparse; one final LF",
              "all_frozen_source_hashes_verified": True, "programs": rows,
              "old_envelope": {"tokens": 256, "ast_nodes": 278,
                               "normalized_bytes": 516},
              "new_envelope": {"tokens": rows[1]["tokens"],
                               "ast_nodes": rows[3]["ast_nodes"],
                               "normalized_bytes": rows[5]["normalized_bytes"]},
              "envelope_is_three_different_programs": True}
    (ROOT / "evidence").mkdir(exist_ok=True)
    (ROOT / "evidence/METRICS.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
