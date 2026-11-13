"""Measure complete selected modules with the pinned CPython normalization."""
from pathlib import Path
import ast
import hashlib
import io
import json
import platform
import tokenize

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    "compact477.py": (273, 305, 477),
    "strict623.py": (340, 385, 623),
    "strict330.py": (330, 379, 641),
    "native600.py": (336, 378, 600),
    "native323.py": (323, 369, 622),
}
SKIP = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
        tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}

def measure(path):
    raw = path.read_bytes()
    normalized = ast.unparse(ast.parse(raw)) + "\n"
    return {
        "tokens": sum(t.type not in SKIP for t in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        "ast_nodes": len(list(ast.walk(ast.parse(normalized)))),
        "normalized_bytes": len(normalized.encode()),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "source_is_normalized": raw == normalized.encode(),
    }

def main():
    rows = []
    for name, expected in EXPECTED.items():
        row = {"path": "checkers/" + name, **measure(ROOT / "checkers" / name)}
        actual = tuple(row[k] for k in ("tokens", "ast_nodes", "normalized_bytes"))
        if actual != expected:
            raise SystemExit(f"Metric mismatch for {name}: {actual}, expected {expected}. "
                             "Exact figures use CPython 3.12.14.")
        rows.append(row)
    report = {
        "python": platform.python_version(),
        "coordinate_order": ["significant_tokens", "ast_nodes", "normalized_bytes"],
        "programs": rows,
        "old_envelopes": {"compact": [244,267,478], "strict": [334,386,628],
                          "native_goal": [324,370,607]},
        "new_envelopes": {"compact": [244,267,477], "strict": [330,379,623],
                          "native_goal": [323,369,600]},
        "envelopes_attained_by_one_program": False,
    }
    (ROOT / "evidence/metrics.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))

if __name__ == "__main__":
    main()

