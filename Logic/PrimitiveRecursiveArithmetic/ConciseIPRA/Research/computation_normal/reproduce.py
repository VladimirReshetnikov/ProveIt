"""Reproduce tests and whole-module metrics; no network or third-party imports."""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import subprocess
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence"
EVIDENCE.mkdir(exist_ok=True)
outputs = {}
for name, path in [
    ("scope_composition", "scope_composition/reproduce.py"),
    ("full_normal", "tests/verify_full_normal.py"),
    ("goal_checkers", "tests/verify_goal_checkers.py"),
    ("fuel", "tests/verify_fuel.py"),
]:
    result = subprocess.run([sys.executable, "-B", str(ROOT / path)], cwd=ROOT,
                            text=True, capture_output=True, timeout=180)
    outputs[name] = {"returncode": result.returncode, "stdout": result.stdout,
                     "stderr": result.stderr}
    if result.returncode:
        print(json.dumps(outputs[name], indent=2))
        raise SystemExit(f"Verification failed: {name}")

programs = [
    ("Compact arity envelope", "scope_composition/reference/compact516.py"),
    ("Public Eq/Q/D baseline", "scope_composition/reference/typed870.py"),
    ("Public Eq/Q/D scope reuse", "code/scope_lexical.py"),
    ("Zero-normal original", "reference/zero_normal3095.py"),
    ("Zero-normal term certificate", "reference/zero_normal3029.py"),
    ("Full-normal initial", "reference/full_initial3048.py"),
    ("Full-normal neutral guard", "code/full_normal.py"),
    ("Full-normal explicit fuel", "code/full_normal_fuel.py"),
    ("Zero-normal goal directed", "code/goal_zero_six.py"),
    ("Full-normal goal directed", "code/goal_full_six.py"),
    ("Full goal directed, fuel", "code/goal_full_six_fuel.py"),
]
normalized_dir = EVIDENCE / "normalized"
normalized_dir.mkdir(exist_ok=True)
metrics = []
ignored = {tokenize.ENDMARKER, tokenize.ENCODING, tokenize.NEWLINE, tokenize.NL,
           tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
for label, relative in programs:
    path = ROOT / relative
    raw = path.read_bytes()
    normalized = (ast.unparse(ast.parse(raw)) + "\n").encode()
    compressed = gzip.compress(normalized, compresslevel=9, mtime=0)
    tokens = [token for token in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
              if token.type not in ignored]
    metrics.append({"label": label, "path": relative, "source_sha256": hashlib.sha256(raw).hexdigest(),
                    "normalized_bytes": len(normalized), "significant_tokens": len(tokens),
                    "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
                    "gzip9_bytes": len(compressed)})
    name = path.stem
    (normalized_dir / (name + ".py")).write_bytes(normalized)
    (normalized_dir / (name + ".py.gz")).write_bytes(compressed)

report = {"python": sys.version, "zlib": zlib.ZLIB_RUNTIME_VERSION,
          "baseline_commit": "d9383325b18d349b8bfdc54ef564c5784cc029ec",
          "verification": outputs, "metrics": metrics}
(EVIDENCE / "reproduction.json").write_text(json.dumps(report, indent=2) + "\n")
(EVIDENCE / "checker_metrics.json").write_text(json.dumps(metrics, indent=2) + "\n")
rows = []
for row in metrics:
    rows.append(f"{row['label']} & {row['normalized_bytes']} & {row['significant_tokens']} & "
                f"{row['ast_nodes']} & {row['gzip9_bytes']} " + r"\\")
tex = "\n".join([
    r"\begin{center}\small",
    r"\begin{tabular}{lrrrr}\toprule",
    r"Complete program & Bytes & Tokens & AST & Gzip 9\\\midrule",
    *rows, r"\bottomrule\end{tabular}", r"\end{center}", ""
])
(EVIDENCE / "metrics_table.tex").write_text(tex)
print(json.dumps({"verification": {k: v["returncode"] for k, v in outputs.items()},
                  "metrics": metrics}, indent=2))
