"""Measure every named complete acceptance module; never mutate evidence."""
import argparse
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


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw.decode("utf-8"))
    for node in ast.walk(tree):
        if (isinstance(node, (ast.Module, ast.FunctionDef,
                              ast.AsyncFunctionDef, ast.ClassDef))
                and node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            del node.body[0]
    source = ast.unparse(tree) + "\n"
    return {
        "path": str(path.relative_to(ROOT)),
        "tokens": sum(t.type not in IGNORED for t in
                      tokenize.generate_tokens(io.StringIO(source).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(source))),
        "normalized_bytes": len(source.encode("utf-8")),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "normalized_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest(),
    }


def collect():
    paths = [ROOT / "atomic/code/atomic_alias.py",
             ROOT / "atomic/code/atomic_alias_small.py"]
    for directory in ("atomic/controls", "strict/checkers", "strict/controls",
                      "reference/compact_controls"):
        paths.extend(sorted((ROOT / directory).glob("*.py")))
    return {
        "python": platform.python_version(),
        "normalization": "Remove actual docstrings, ast.unparse, one final LF",
        "programs": [measure(path) for path in paths],
        "compact_incumbent_envelope": [248, 270, 479],
        "old_strict_native_envelope": [342, 391, 637],
        "new_strict_native_envelope": [338, 386, 633],
        "envelope_uses_different_programs": True,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    output = json.dumps(collect(), indent=2) + "\n"
    if args.output:
        args.output.write_text(output, encoding="utf-8")
    else:
        print(output, end="")
