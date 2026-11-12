"""Measure complete acceptance modules under one fixed normalization."""
import ast
import csv
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
PROFILES = [
    ("Zero-normal kernel", 7, "reference/zero_seven.py"),
    ("Witness-selected control", 6, "reference/witness_six.py"),
    ("Reflexive-base proposal", 6, "code/checker.py"),
]


def main():
    rows = []
    excluded = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
                tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
                tokenize.ENDMARKER}
    destination = ROOT / "evidence" / "normalized"
    destination.mkdir(parents=True, exist_ok=True)
    for name, rules, path in PROFILES:
        source = (ROOT / path).read_text()
        tree = ast.parse(source)
        normalized = ast.unparse(tree) + "\n"
        data = normalized.encode()
        compressed = gzip.compress(data, compresslevel=9, mtime=0)
        basename = Path(path).name
        (destination / basename).write_bytes(data)
        (destination / (basename + ".gz")).write_bytes(compressed)
        rows.append(dict(
            profile=name, rules=rules, path=path,
            tokens=sum(t.type not in excluded
                       for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
            ast_nodes=sum(1 for _ in ast.walk(tree)),
            normalized_bytes=len(data), gzip9_bytes=len(compressed),
            source_sha256=hashlib.sha256(source.encode()).hexdigest(),
            normalized_sha256=hashlib.sha256(data).hexdigest()))
    report = dict(python=sys.version, normalization="ast.unparse(ast.parse(source)) + LF",
                  gzip="level 9; mtime 0; wrapper included; informational",
                  profiles=rows)
    (ROOT / "evidence" / "metrics.json").write_text(json.dumps(report, indent=2) + "\n")
    with (ROOT / "evidence" / "metrics.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    lines = [r"\begin{center}", r"\small",
             r"\begin{tabular}{lrrrrr}", r"\toprule",
             r"Complete checker & Rules & Tokens & AST & Bytes & Gzip-9\\",
             r"\midrule"]
    for row in rows:
        lines.append(row["profile"] + " & " + " & ".join(
            str(row[k]) for k in ["rules", "tokens", "ast_nodes",
                                  "normalized_bytes", "gzip9_bytes"]) + r"\\")
    lines += [r"\bottomrule", r"\end{tabular}", r"\end{center}"]
    (ROOT / "evidence" / "metrics_table.tex").write_text("\n".join(lines) + "\n")
    print(json.dumps(rows, indent=2))
    return report


if __name__ == "__main__":
    main()
