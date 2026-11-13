#!/usr/bin/env python3
"""Replay the new kernels and measurements. Use --census for the full source audit."""
import argparse
import ast
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
           tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}

def measured(path):
    source = ast.unparse(ast.parse(path.read_text())) + "\n"
    return {"tokens": sum(t.type not in IGNORED for t in
                          tokenize.generate_tokens(io.StringIO(source).readline)),
            "ast_nodes": len(list(ast.walk(ast.parse(source)))),
            "normalized_bytes": len(source.encode())}

def run(relative):
    script = ROOT / relative
    p = subprocess.run([sys.executable, str(script)], cwd=script.parent,
                       capture_output=True, text=True)
    if p.returncode:
        raise RuntimeError(relative + "\n" + p.stdout + p.stderr)
    return json.loads(p.stdout)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--census", action="store_true")
    args = parser.parse_args()
    result = {"python": sys.version, "compact": run("implementation/compact/reproduce.py"),
              "uniqueness": run("implementation/uniqueness/verify.py")}
    result["incoming_profiles"] = {name: measured(ROOT / "reference" / ("incoming_" + name + ".py"))
                                   for name in ("tokens", "ast", "bytes")}
    normalized = ROOT / "implementation/uniqueness/kernel_normalized.py"
    result["normalized_uniqueness_executable"] = measured(normalized)
    if result["normalized_uniqueness_executable"] != result["uniqueness"]["checker_metrics"]:
        raise RuntimeError("normalized executable differs from documented metrics")
    for fixture in (ROOT / "implementation/uniqueness/certificates").glob("*.json"):
        p = subprocess.run([sys.executable, str(normalized)], input=fixture.read_text(),
                           capture_output=True, text=True)
        if p.returncode or p.stdout != "ACCEPT\n":
            raise RuntimeError("normalized executable rejected " + fixture.name)
    result["normalized_executable_positive_replays"] = 8
    if args.census:
        result["census"] = run("reference/research_census/reproduce_audit.py")
    (ROOT / "evidence/reproduction.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"compact": result["compact"], "uniqueness_metrics":
                      result["uniqueness"]["checker_metrics"],
                      "positive_certificates": len(result["uniqueness"]["positive_certificates"]),
                      "negative_checks": len(result["uniqueness"]["negative_checks"]),
                      "incoming_profiles": result["incoming_profiles"],
                      "census": result.get("census")}, indent=2))

if __name__ == "__main__":
    main()

