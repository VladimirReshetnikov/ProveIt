#!/usr/bin/env python3
"""Generate exact tables and compile the complete LaTeX report."""
import argparse
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
E = ROOT / "evidence"

def number(n):
    return f"{n:,}"

def table(rows):
    out = [r"\begin{tabular}{@{}lrrrr@{}}", r"\toprule",
           r"Complete program & Tokens & AST & Bytes & Gzip-9\\",
           r"\midrule"]
    for title, record in rows:
        out.append(title + " & " + " & ".join(number(record[key]) for key in
                   ("tokens", "ast_nodes", "normalized_bytes", "gzip9_bytes")) + r"\\")
    out += [r"\bottomrule", r"\end{tabular}"]
    return "\n".join(out) + "\n"

def prepare():
    metrics = json.loads((E / "metrics.json").read_text())
    data = {item["file"]: item for item in metrics["programs"]}
    result = json.loads((E / "validation.json").read_text())
    if result["status"] != "PASS" or result["failures"]:
        raise SystemExit("The verification receipt must pass before publication.")
    primary = [
        ("Full native control", data["reference/native_typed_full.py"]),
        ("Full native, shared validator", data["code/native_typed_full.py"]),
        ("Eq/D matched control", data["reference/native_typed_eqd.py"]),
        ("Eq/D, shared validator", data["code/native_typed_eqd.py"]),
    ]
    compact = [
        ("Incoming token profile", data["reference/guarded_tokens.py"]),
        ("New token profile", data["code/guarded_tokens.py"]),
        ("Incoming AST profile", data["reference/guarded_ast.py"]),
        ("New AST profile", data["code/guarded_ast.py"]),
        ("Incoming byte profile", data["reference/guarded_bytes.py"]),
        ("New byte profile", data["code/guarded_bytes.py"]),
        ("Incoming goal-checked", data["reference/guarded_goal_checked.py"]),
        ("New goal-checked", data["code/guarded_goal_checked.py"]),
    ]
    (E / "primary_table.tex").write_text(table(primary))
    (E / "compact_table.tex").write_text(table(compact))
    macros = {
        "FullOldBytes": data["reference/native_typed_full.py"]["normalized_bytes"],
        "FullNewBytes": data["code/native_typed_full.py"]["normalized_bytes"],
        "EQDoldBytes": data["reference/native_typed_eqd.py"]["normalized_bytes"],
        "EQDnewBytes": data["code/native_typed_eqd.py"]["normalized_bytes"],
        "CompactNewTokens": data["code/guarded_tokens.py"]["tokens"],
        "CompactNewAST": data["code/guarded_ast.py"]["ast_nodes"],
        "CompactNewBytes": data["code/guarded_bytes.py"]["normalized_bytes"],
        "ValidationExecutions": result["process_executions"],
        "ValidationFailures": len(result["failures"]),
    }
    (E / "metrics_macros.tex").write_text("\n".join(
        r"\newcommand{\%s}{%s}" % (key, number(value))
        for key, value in macros.items()) + "\n")
    return macros

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tables-only", action="store_true")
    args = parser.parse_args()
    macros = prepare()
    if not args.tables_only:
        for _ in range(3):
            run = subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                 "-file-line-error", "ipra_validated_core.tex"],
                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, timeout=120)
            if run.returncode:
                print(run.stdout[-7000:])
                raise SystemExit(run.returncode)
        (E / "latex_build.txt").write_text(run.stdout)
    print(json.dumps({"tables": "generated", "pdf": not args.tables_only,
                      "measurements": macros}, indent=2))

if __name__ == "__main__":
    main()

