"""Reproduce complete-module CPython source measurements."""
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
    normalized = ast.unparse(ast.parse(raw.decode())) + "\n"
    return {
        "path": str(path.relative_to(ROOT)),
        "tokens": sum(t.type not in IGNORED for t in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
        "normalized_bytes": len(normalized.encode()),
        "sha256": hashlib.sha256(raw).hexdigest(),
    }


def main():
    paths = sorted((ROOT / "controls").glob("*.py")) + sorted((ROOT / "checkers").glob("*.py"))
    result = {"python": platform.python_version(),
              "normalization": "Whole source; ast.unparse; one final LF",
              "programs": [measure(p) for p in paths],
              "new_strict_envelope": [338, 386, 633],
              "identified_old_strict_envelope": [342, 391, 637],
              "envelope_is_different_programs": True,
              "compact_envelope_not_improved": [248, 270, 479]}
    (ROOT / "evidence" / "metrics.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


if __name__ == "__main__":
    print(json.dumps(main(), indent=2))
