#!/usr/bin/env python3
"""Inventory source statements and inspect actual Lean audit output.

This is a status audit, not a mathematical proof checker. It never counts a
definition named Target as a theorem.
"""
from pathlib import Path
import csv
import json
import re

ROOT = Path(__file__).resolve().parents[1]

def remove_comments(source):
    out = []
    i = 0
    depth = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if source[i] == "\n":
                out.append("\n")
            i += 1
        elif source.startswith("--", i):
            stop = source.find("\n", i)
            i = len(source) if stop < 0 else stop
        else:
            out.append(source[i])
            i += 1
    return "".join(out)

def main():
    modules = []
    forbidden = []
    for path in sorted((ROOT / "lean").glob("*.lean")):
        text = remove_comments(path.read_text())
        names = re.findall(r"^theorem\s+(\w+)", text, re.M)
        targets = re.findall(r"^def\s+(\w*Target)\b", text, re.M)
        problems = re.findall(r"\b(?:sorry|admit)\b|^\s*axiom\b", text, re.M)
        if problems:
            forbidden.append({"file": path.name, "tokens": problems})
        log = ROOT / "validation" / (path.stem + "_checked.log")
        raw = log.read_text() if log.exists() else ""
        audits = re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", raw)
        axioms = sorted({a.strip() for _, group in audits for a in group.split(",") if a.strip()})
        modules.append({
            "file": str(path.relative_to(ROOT)),
            "theorem_declarations": len(names),
            "theorems": names,
            "unproved_target_definitions": targets,
            "compiled_log": str(log.relative_to(ROOT)) if log.exists() else None,
            "axiom_reports": len(audits),
            "used_axioms_in_printed_reports": axioms
        })
    if forbidden:
        raise SystemExit(json.dumps({"forbidden_declarations": forbidden}, indent=2))
    rows = []
    for path in sorted((ROOT / "paper" / "sections").glob("*.tex")):
        source = path.read_text()
        for ordinal, match in enumerate(re.finditer(r"\\begin\{(theorem|lemma|proposition|corollary)\}(?:\[([^\]]*)\])?", source), 1):
            title = match.group(2) or "(untitled)"
            after = source[match.end():]
            label = re.match(r"\s*\\label\{([^}]+)\}", after)
            rows.append({
                "section_file": path.name,
                "ordinal": ordinal,
                "kind": match.group(1),
                "title_latex": title,
                "label": label.group(1) if label else "",
                "human_proof": "included",
                "object_ipra_derivation": "not delivered",
                "scope": (
                    "arithmetic proof rule" if path.name.startswith("02") else
                    "metatheoretic computability obstruction" if title.startswith("L06") else
                    "finite algebraic theorem or finite-presheaf theorem" if path.name.startswith("05") else
                    "finite topology" if path.name.startswith("03") else
                    "equipped metric schema" if path.name.startswith("04") else
                    "finite or equipped dimension theorem" if path.name.startswith("06") else
                    "finite chain or rational-field sphere theorem" if path.name.startswith("07") else
                    "qualified finite replacement"
                )
            })
    with (ROOT/"data"/"theorem_ledger.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)
    result = {
        "status": "passed",
        "human_numbered_results": len(rows),
        "topology_and_support_results_excluding_arithmetic_rules": len(rows)-2,
        "lean_theorem_declarations": sum(m["theorem_declarations"] for m in modules),
        "all_lean_theorems_audited": all(m["axiom_reports"] == m["theorem_declarations"] for m in modules),
        "lean_proof_holes_or_user_axioms": forbidden,
        "modules": modules,
        "interpretation": "Semantic Lean checks and human proofs. No complete Prf PRAAx endpoint for the collection is delivered."
    }
    (ROOT/"validation"/"source_audit.json").write_text(json.dumps(result, indent=2)+"\n")
    if not result["all_lean_theorems_audited"]:
        raise SystemExit(json.dumps({"status":"missing axiom reports","modules":modules},indent=2))
    if any("sorryAx" in m["used_axioms_in_printed_reports"] or "Classical.choice" in m["used_axioms_in_printed_reports"] for m in modules):
        raise SystemExit("Unexpected theorem axiom; inspect source_audit.json")
    print(json.dumps({k:result[k] for k in ("status","human_numbered_results","lean_theorem_declarations","all_lean_theorems_audited")},indent=2))

if __name__ == "__main__":
    main()

