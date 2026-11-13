"""Measure complete standalone modules with the pinned CPython protocol."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
        tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
PROGRAMS = [
    ("Compact baseline: tokens", "controls/tokens241.py", "compact-control"),
    ("Compact baseline: AST", "controls/ast262.py", "compact-control"),
    ("Compact baseline: bytes", "controls/bytes469.py", "compact-control"),
    ("Inherited return: tokens", "code/inherited_tokens240.py", "inherited"),
    ("Inherited return: AST", "code/inherited_ast261.py", "inherited"),
    ("New offset procedure", "code/checker_compact462.py", "new-compact"),
    ("Strict baseline: tokens", "controls/scope_strict_tokens.py", "strict-control"),
    ("Strict baseline: AST", "controls/scope_strict_ast.py", "strict-control"),
    ("Strict baseline: bytes", "controls/checker_strict606.py", "strict-control"),
    ("New strict: tokens", "code/checker_strict_tokens_iterable.py", "new-strict"),
    ("New strict: AST", "code/checker_strict_ast_iterable.py", "new-strict"),
    ("New strict: bytes", "code/checker_strict_procedure.py", "new-strict"),
    ("Native baseline: bytes", "controls/checker_native579.py", "native-control"),
    ("New native procedure", "code/checker_native_procedure.py", "new-native"),
]
EXPECTED = {
    "code/inherited_tokens240.py": (240, 266, 551, 333),
    "code/inherited_ast261.py": (242, 261, 563, None),
    "code/checker_compact462.py": (267, 298, 462, 310),
    "code/checker_strict_tokens_iterable.py": (320, 371, 630, 398),
    "code/checker_strict_ast_iterable.py": (327, 362, 639, 399),
    "code/checker_strict_procedure.py": (330, 372, 600, 387),
    "code/checker_native_procedure.py": (324, 366, 573, 362),
}

def measure(label, relative, group):
    raw = (ROOT / relative).read_bytes()
    tree = ast.parse(raw)
    normalized = (ast.unparse(tree) + "\n").encode("utf-8")
    compressed = gzip.compress(normalized, compresslevel=9, mtime=0)
    row = dict(label=label, path=relative, group=group,
               tokens=sum(t.type not in SKIP for t in
                          tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
               ast_nodes=len(list(ast.walk(tree))),
               normalized_bytes=len(normalized), gzip9_bytes=len(compressed),
               source_sha256=hashlib.sha256(raw).hexdigest(),
               normalized_sha256=hashlib.sha256(normalized).hexdigest())
    if relative.startswith("code/"):
        (ROOT / (relative + ".gz")).write_bytes(compressed)
    return row

def table(rows, title, label):
    lines = [r"\begin{table}[htbp]", r"\centering\small",
             r"\begin{tabular}{@{}lrrrr@{}}", r"\toprule",
             r"Complete module & Tokens & AST & Bytes & Gzip-9\\", r"\midrule"]
    old_group = None
    for row in rows:
        if old_group is not None and old_group != row["group"]:
            lines.append(r"\midrule")
        old_group = row["group"]
        values = [row[k] for k in ("tokens", "ast_nodes", "normalized_bytes", "gzip9_bytes")]
        lines.append(row["label"] + " & " + " & ".join(map(str, values)) + r"\\")
    lines += [r"\bottomrule", r"\end{tabular}",
              r"\caption{" + title + "}", r"\label{" + label + "}", r"\end{table}", ""]
    return "\n".join(lines)

def main():
    rows = [measure(*p) for p in PROGRAMS]
    report = dict(python=sys.version,
                  normalization="ast.unparse(ast.parse(whole_source)) plus one LF; no docstring removal",
                  gzip=dict(compresslevel=9, mtime=0), programs=rows)
    (ROOT / "evidence/metrics.json").write_text(json.dumps(report, indent=2) + "\n")
    if sys.version_info[:2] == (3, 12):
        for row in rows:
            expected = EXPECTED.get(row["path"])
            if expected:
                actual = tuple(row[k] for k in ("tokens", "ast_nodes", "normalized_bytes", "gzip9_bytes"))
                assert all(e is None or e == a for e, a in zip(expected, actual)), (row, expected)
    compact = table(rows[:6],
        "Compact profiles. The pinned coordinate envelope is 241/262/469. "
        "The consolidated envelope is 240/261/462; its token and AST records "
        "are inherited unchanged from the earlier return-reservation package.",
        "tab:compact")
    strict = table(rows[6:],
        "Stronger validation contracts, compared separately. "
        "The fully validated envelope improves from 322/364/606 to 320/362/600. "
        "The native goal-validated byte profile improves from 579 to 573.",
        "tab:validated")
    (ROOT / "metrics.tex").write_text(compact + "\n" + strict)
    print(json.dumps({"python": sys.version.split()[0], "programs": [
        {k: row[k] for k in ("path", "tokens", "ast_nodes", "normalized_bytes", "gzip9_bytes")}
        for row in rows]}, indent=2))

if __name__ == "__main__":
    main()

