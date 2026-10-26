#!/usr/bin/env python3
"""Reproduce descriptive metrics for the pinned active Lean source tree.

Usage: python3 audit_sources.py /path/to/ProveIt /path/to/output
Only Computability/DiophantineConsistency/Lean is included. Historical
manuscript copies and generated build products are deliberately excluded.
Declaration spans are lexical estimates, not Lean AST or proof-term sizes.
"""
from __future__ import annotations
import argparse
import collections
import csv
import hashlib
import json
from pathlib import Path
import re
import subprocess

PIN = "60e9c5d620c6c387d932876cfa2d9376f64ea56c"
ROOT = Path("Computability/DiophantineConsistency/Lean")
TACTICS = ["simp", "simpa", "simp_all", "omega", "ring", "ring_nf",
           "nlinarith", "linarith", "norm_num", "decide", "native_decide",
           "aesop", "funext", "fin_cases", "rcases", "congr", "subst"]


def strip_comments_and_strings(s: str) -> str:
    """Mask nested Lean comments and strings, preserving line positions."""
    out, i, depth = [], 0, 0
    while i < len(s):
        if depth:
            if s.startswith("/-", i):
                depth += 1; out.extend("  "); i += 2
            elif s.startswith("-/", i):
                depth -= 1; out.extend("  "); i += 2
            else:
                out.append("\n" if s[i] == "\n" else " "); i += 1
        elif s.startswith("/-", i):
            depth = 1; out.extend("  "); i += 2
        elif s.startswith("--", i):
            j = s.find("\n", i)
            if j == -1: j = len(s)
            out.extend(" " * (j - i)); i = j
        elif s[i] == '"':
            out.append(" "); i += 1
            while i < len(s):
                c = s[i]; out.append("\n" if c == "\n" else " "); i += 1
                if c == "\\" and i < len(s):
                    out.append("\n" if s[i] == "\n" else " "); i += 1
                elif c == '"': break
        else:
            out.append(s[i]); i += 1
    return "".join(out)


def write_csv(path: Path, rows: list[dict]) -> None:
    if not rows: return
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("repository", type=Path)
    ap.add_argument("output", type=Path)
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    commit = subprocess.check_output(
        ["git", "-C", str(args.repository), "rev-parse", "HEAD"], text=True).strip()
    files, declarations, edges = [], [], []
    counts = collections.Counter()
    decl_pattern = re.compile(
        r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*"
        r"(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([^\s(:{]+)", re.M)
    for p in sorted((args.repository / ROOT).rglob("*.lean")):
        raw = p.read_bytes(); s = raw.decode("utf-8"); clean = strip_comments_and_strings(s)
        rel = str(p.relative_to(args.repository))
        check = "checks" in p.relative_to(args.repository / ROOT).parts or p.stem.endswith(("Checks", "Audit"))
        generated = bool(re.search(r"\bgenerated\b", s[:2500], re.I))
        local = {t: len(re.findall(r"\b" + t + r"\b", clean)) for t in TACTICS}
        row = dict(path=rel, category="check/audit" if check else "library/aggregate",
                   header_mentions_generated=generated, physical_lines=len(s.splitlines()),
                   nonblank_code_lines=sum(bool(x.strip()) for x in clean.splitlines()),
                   utf8_bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest(), **local)
        files.append(row)
        if not check: counts.update(local)
        matches = list(decl_pattern.finditer(clean))
        for j, m in enumerate(matches):
            start = clean.count("\n", 0, m.start()) + 1
            endpos = matches[j+1].start() if j+1 < len(matches) else len(clean)
            end = clean.count("\n", 0, endpos) + 1
            declarations.append(dict(path=rel, kind=m[1], name=m[2], start_line=start,
                                     next_declaration_line=end, estimated_span_lines=end-start,
                                     check_or_audit=check))
        for target in re.findall(r"^import\s+(\S+)", clean, re.M):
            edges.append(dict(source=rel, imported_module=target))
    library = [r for r in files if r["category"] == "library/aggregate"]
    trust = collections.Counter()
    for row in files:
        s = strip_comments_and_strings((args.repository / row["path"]).read_text())
        trust.update(re.findall(r"\b(?:sorry|axiom|native_decide)\b", s))
    report = dict(commit=commit, expected_commit=PIN, commit_matches=commit == PIN,
                  scope=str(ROOT), files=len(files), physical_lines=sum(r["physical_lines"] for r in files),
                  library_or_aggregate_files=len(library),
                  library_or_aggregate_lines=sum(r["physical_lines"] for r in library),
                  check_or_audit_files=len(files)-len(library),
                  check_or_audit_lines=sum(r["physical_lines"] for r in files if r not in library),
                  lexical_tactic_counts_library=dict(counts), lexical_trust_tokens_all=dict(trust),
                  largest_library_files=sorted(library, key=lambda r:r["physical_lines"], reverse=True)[:25],
                  caveats=["Line counts include comments and blanks unless labeled nonblank_code_lines.",
                           "Tactic counts are lexical token counts after comment/string masking.",
                           "The token decide includes bound proofs in data, not only theorem proofs.",
                           "Header detection of generated files is a heuristic, not an exhaustive classification.",
                           "Declaration spans include following commands/comments and are only prioritization hints.",
                           "No full repository build or axiom audit is implied by these source metrics."])
    (args.output / "source_metrics.json").write_text(json.dumps(report, indent=2) + "\n")
    write_csv(args.output / "source_files.csv", files)
    write_csv(args.output / "declaration_spans.csv", sorted(declarations, key=lambda r:r["estimated_span_lines"], reverse=True))
    write_csv(args.output / "imports.csv", edges)
    print(json.dumps({k:report[k] for k in ["commit", "files", "physical_lines", "library_or_aggregate_files",
                                          "library_or_aggregate_lines", "check_or_audit_files", "check_or_audit_lines",
                                          "lexical_trust_tokens_all"]}, indent=2))


if __name__ == "__main__":
    main()
