"""Measure every complete acceptance module; no checker imports this file."""
from pathlib import Path
import ast
import hashlib
import io
import json
import platform
import tokenize

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    "code/checker_tokens.py": (249, 278, 607),
    "code/checker_ast.py": (255, 271, 606),
    "code/checker_bytes.py": (267, 299, 495),
    "code/checker_native.py": (342, 391, 666),
    "controls/incumbent_tokens.py": (251, 283, 605),
    "controls/incumbent_ast.py": (262, 273, 572),
    "controls/checker_bytes_499.py": (265, 301, 499),
    "controls/checker_native_673.py": (344, 393, 673),
}
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


class RemoveDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if node.body and isinstance(node.body[0], ast.Expr):
            value = node.body[0].value
            if isinstance(value, ast.Constant) and isinstance(value.value, str):
                node.body = node.body[1:]
        return node
    visit_Module = clean
    visit_FunctionDef = clean
    visit_AsyncFunctionDef = clean
    visit_ClassDef = clean


def measure(relative):
    source = (ROOT / relative).read_bytes()
    tree = RemoveDocstrings().visit(ast.parse(source))
    text = ast.unparse(tree) + "\n"
    return {
        "path": relative,
        "significant_tokens": sum(t.type not in SKIP for t in
            tokenize.generate_tokens(io.StringIO(text).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(text))),
        "normalized_bytes": len(text.encode()),
        "sha256": hashlib.sha256(source).hexdigest(),
        "normalized_sha256": hashlib.sha256(text.encode()).hexdigest(),
    }


def main():
    rows = [measure(p) for p in EXPECTED]
    for r in rows:
        actual = tuple(r[k] for k in
                       ("significant_tokens", "ast_nodes", "normalized_bytes"))
        if actual != EXPECTED[r["path"]]:
            raise ValueError((r["path"], actual, EXPECTED[r["path"]]))
    receipt = {"python": platform.python_version(),
               "reference_python": "3.12.14", "rows": rows,
               "old_compact_envelope": [251, 273, 499],
               "new_compact_envelope": [249, 271, 495],
               "one_program_attains_all_coordinates": False,
               "all_expected_measurements_match": True}
    (ROOT / "evidence/metrics.json").write_text(json.dumps(receipt, indent=2)+"\n")
    names = ["Three-field token profile", "Three-field AST profile",
             "Four-field byte profile", "Fully validated native profile",
             "Incumbent token profile", "Incumbent AST profile",
             "Incumbent byte profile", "Matched native control"]
    lines = [r"\begin{center}\small",
             r"\begin{tabular}{@{}lrrr@{}}", r"\toprule",
             r"Complete module & Tokens & AST nodes & Bytes\\", r"\midrule"]
    for name, r in zip(names, rows):
        lines.append(f"{name} & {r['significant_tokens']} & {r['ast_nodes']} & {r['normalized_bytes']}"+r"\\")
    lines += [r"\bottomrule", r"\end{tabular}", r"\end{center}"]
    (ROOT / "evidence/metrics_table.tex").write_text("\n".join(lines)+"\n")
    print(json.dumps({"measured_modules": len(rows),
                      "compact_envelope": [249, 271, 495],
                      "all_expected_measurements_match": True}))
    return receipt


if __name__ == "__main__":
    main()
