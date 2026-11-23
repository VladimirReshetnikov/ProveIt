#!/usr/bin/env python3
"""Generate the report's exact result inventory from its LaTeX sources."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHAPTERS = ["foundations", "elementary", "quadratic", "diophantine",
            "analytic", "algebraic", "transcendence"]
ENV = re.compile(r"\\begin\{(theorem|lemma|corollary|proposition)\}(?:\[(.*?)\])?(.*?)\\end\{\1\}", re.S)
entries = []
counts = {}
for section, chapter in enumerate(CHAPTERS, 1):
    relative = f"chapters/{chapter}.tex"
    source = (ROOT / relative).read_text()
    results = list(ENV.finditer(source))
    counts[chapter] = len(results)
    for number, match in enumerate(results, 1):
        kind, title, statement = match.groups()
        label = re.search(r"\\label\{([^}]+)\}", statement)
        if not label:
            raise ValueError(f"Missing result label in {relative}: {title}")
        title = re.sub(r"\s+", " ", title or kind.title()).strip()
        statement = re.sub(r"\\label\{[^}]+\}", "", statement).strip()
        entries.append({"id": label.group(1), "number": f"{section}.{number}",
                        "kind": kind, "title_latex": title,
                        "statement_latex": statement, "source": relative,
                        "proof_status": "human proof with explicit iPRA reduction; Lean uncompiled"})
labels = [e["id"] for e in entries]
if len(set(labels)) != len(labels):
    raise ValueError("Duplicate theorem labels")
foundations = counts["foundations"]
payload = {"total_numbered_results": len(entries),
           "foundational_results": foundations,
           "number_theoretic_results": len(entries) - foundations,
           "counts_by_chapter": counts,
           "counting_policy": "Distinct numbered theorem/lemma/corollary/proposition blocks; consequences within one block are not counted separately.",
           "results": entries}
(ROOT / "theorem_inventory.json").write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n")
(ROOT / "metrics.tex").write_text(
    f"\\newcommand{{\\ResultCount}}{{{len(entries)}}}\n"
    f"\\newcommand{{\\FoundationCount}}{{{foundations}}}\n"
    f"\\newcommand{{\\NumberTheoryCount}}{{{len(entries)-foundations}}}\n")
lines = [r"\begin{longtable}{p{0.16\linewidth}p{0.75\linewidth}}",
         r"\toprule Result & Statement title\\", r"\midrule\endhead"]
for entry in entries:
    lines.append(f"{entry['kind'].title()}~\\ref{{{entry['id']}}} & {entry['title_latex']}\\\\")
lines.extend([r"\bottomrule", r"\end{longtable}"])
(ROOT / "inventory.tex").write_text("\n".join(lines) + "\n")
print(json.dumps({k: v for k, v in payload.items() if k != "results"}, indent=2))
