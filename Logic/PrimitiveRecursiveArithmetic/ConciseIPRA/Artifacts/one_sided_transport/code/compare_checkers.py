# Generate the matched M7 control, changing only the equality branch of C7.
import ast
import difflib
import gzip
import hashlib
import io
import json
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parent

OLD = '''    elif op == "x":
        require(len(p) == 6 and a[0] == "=")
        s, t, f, major, minor = p[1:]
        require(term(s, n) and s != ZERO and term(t, n) and
                term(f, n + 1) and a[2] == replace(f, n, t))
        check(["=", s, t], major, context, n)
        check(["=", replace(f, n, s), a[1]], minor, context, n)
'''

NEW = '''    elif op == "x":
        require(len(p) == 7 and a[0] == "=")
        s, t, f, g, major, minor = p[1:]
        require(term(s, n) and s != ZERO and term(t, n) and
                term(f, n + 1) and term(g, n + 1) and
                a == ["=", replace(f, n, t), replace(g, n, t)])
        check(["=", s, t], major, context, n)
        check(["=", replace(f, n, s), replace(g, n, s)], minor, context, n)
'''


def metrics(source):
    normalized = ast.unparse(ast.parse(source)) + "\n"
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {"tokens": sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
            "ast_nodes": len(list(ast.walk(ast.parse(normalized)))),
            "normalized_bytes": len(normalized.encode()),
            "gzip9_normalized": len(gzip.compress(normalized.encode(), compresslevel=9, mtime=0)),
            "raw_sha256": hashlib.sha256(source.encode()).hexdigest()}


def main():
    c7 = (ROOT / "c7_checker.py").read_text()
    if c7.count(OLD) != 1:
        raise ValueError("C7 equality branch changed; review the control generator")
    m7 = c7.replace(OLD, NEW)
    (ROOT / "m7_control.py").write_text(m7)
    cm, mm = metrics(c7), metrics(m7)
    coordinates = ["tokens", "ast_nodes", "normalized_bytes", "gzip9_normalized"]
    report = {"python": sys.version,
              "normalization": "ast.unparse(ast.parse(source)) + newline",
              "gzip": "gzip.compress(normalized UTF-8, compresslevel=9, mtime=0)",
              "change_scope": "Only the equality branch; same opcode spelling x",
              "c7": cm, "matched_m7": mm,
              "c7_minus_m7": {k: cm[k] - mm[k] for k in coordinates},
              "percent_reduction_from_m7": {k: round(100 * (mm[k] - cm[k]) / mm[k], 4) for k in coordinates},
              "frontier_record_claim": False}
    (ROOT / "metrics_delta.json").write_text(json.dumps(report, indent=2) + "\n")
    difference = "".join(difflib.unified_diff(c7.splitlines(True), m7.splitlines(True),
                                             fromfile="c7_checker.py", tofile="m7_control.py"))
    (ROOT / "matched_control.diff").write_text(difference)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
