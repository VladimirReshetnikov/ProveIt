#!/usr/bin/env python3
"""Inventory prior proof-simplification manuscripts as inert data.

Does not execute any code from the reviewed repository or its archives.
Run from this directory or pass --repo and --out explicitly.
"""
import argparse
import hashlib
import json
import re
import zipfile
from pathlib import Path

PIN = "9f35798db4a63c25e435fca14d75931144657d7e"
REL = "Computability/DiophantineConsistency/research/lean-proof-simplification"
MAIN = {
    "a": ["report.tex"], "b": ["report.tex"], "c": ["report.tex"],
    "d": ["report.tex"], "e": ["report/report.tex"],
    "f": ["report/sections/*.tex"], "g": ["report.tex"],
    "h": ["lean-proof-simplification-review.tex"], "i": ["report.tex"],
    "j": ["report.tex"], "k": ["report.tex"], "l": ["report/report.tex"],
    "m": ["report/additional_lean_simplifications.tex"],
    "n": ["report/sections/*.tex"], "o": ["report/report.tex"],
    "p": ["report.tex"], "q": ["report/new-proof-simplifications.tex"],
    "r": ["report.tex"], "s": ["report.tex"],
    "t": ["report/sections/*.tex"], "u": ["report.tex"],
    "v": ["report/sections/*.tex"], "w": ["report.tex"],
}
INCOMING = {
    "I1": "Lean_Proof_Simplification_Post_Adoption_2026-10-26.zip",
    "I2": "ProveIt_Additional_Lean_Simplifications_2026-10-26.zip",
    "I3": "diophantine-lean-further-deltas-2026-10-26.zip",
    "I4": "diophantine-lean-proof-refinements-2026-10-26.zip",
    "I5": "proveit-lean-structural-simplifications-2026-10-26.zip",
}
TERMS = {
    "new_order_modules": r"ControllerPowerCoordinates|CurrentControllerUnits|CurrentPowerCoordinates|PrimePowerOrder|CurrentAuxiliaryOrder",
    "order_lifting": r"\bprime.?power\b|\borderOf\b|multiplicative order|exact order|principal.?unit|padicVal|\bvaluation\b",
    "translation_subset_sums": r"subset.?sum|interval.?sum|\btorsor\b|cardinality.{0,50}unit|unit.{0,50}cardinality",
    "radical_gcd": r"\bradical\b|\bgcd\b|\bCoprime\b|\bIsUnit\b",
}


def record(source, data):
    text = data.decode("utf-8", "replace")
    headings = []
    for line, content in enumerate(text.splitlines(), 1):
        if re.match(r"\s*\\(?:(?:sub)*section\*?|pageheading|paragraph)\{", content):
            headings.append({"line": line, "text": content.strip()})
    return {"source": source, "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest(), "headings": headings}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent / "ProveIt")
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    base = args.repo / REL
    packets = []
    texts = []
    for letter, globs in MAIN.items():
        folder = base / ("2026-10-26" + letter)
        files = sorted({p for pattern in globs for p in folder.glob(pattern)})
        packets.append({"id": letter, "location": str(folder.relative_to(args.repo)),
                        "primary_narratives": [record(str(p.relative_to(args.repo)), p.read_bytes()) for p in files]})
    for p in sorted(base.rglob("*")):
        if p.is_file() and p.suffix.lower() in {".md", ".tex", ".lean", ".txt"}:
            texts.append((str(p.relative_to(args.repo)), p.read_text(errors="replace")))
    for ident, name in INCOMING.items():
        archive = args.repo / "docs/incoming" / name
        data = archive.read_bytes()
        with zipfile.ZipFile(archive) as z:
            members = [i for i in z.infolist() if not i.is_dir()]
            manuscripts = []
            for item in members:
                n = item.filename
                source = str(archive.relative_to(args.repo)) + "::" + n
                if Path(n).suffix.lower() in {".md", ".tex", ".lean", ".txt"}:
                    text = z.read(n).decode("utf-8", "replace")
                    texts.append((source, text))
                if n.endswith(".tex") and ("/report/" in n or n.endswith("/report.tex")):
                    manuscripts.append(record(source, z.read(n)))
            packets.append({"id": ident, "location": str(archive.relative_to(args.repo)),
                            "sha256": hashlib.sha256(data).hexdigest(),
                            "archive_bytes": len(data), "member_count": len(members),
                            "primary_narratives": manuscripts})
    hits = {}
    for label, pattern in TERMS.items():
        regex = re.compile(pattern, re.IGNORECASE)
        hits[label] = [{"source": source, "line": i, "text": line[:600]}
                       for source, text in texts
                       for i, line in enumerate(text.splitlines(), 1)
                       if regex.search(line)]
    readme = args.repo / "docs/incoming/README.md"
    data = {
        "baseline_commit": PIN,
        "interpretation": "All prior proposals, including optional and uncompiled ones, are assumed applied for novelty screening. This is a union of contracts, not a compatible compiled patch set.",
        "coverage": {"placed_packets": 23, "incoming_archives": 5,
                     "text_members_searched": len(texts),
                     "primary_narrative_files": sum(len(p["primary_narratives"]) for p in packets)},
        "incoming_readme": record(str(readme.relative_to(args.repo)), readme.read_bytes()),
        "packets": packets,
        "targeted_term_hits": hits,
        "limitations": "Headings and keyword hits support routing and reproducibility. Semantic novelty decisions additionally require reading the relevant sections; lexical absence is not a global priority proof. Archived source snapshots are not themselves new proposals. Unrelated historical manuscripts linked transitively by README were not all rereviewed.",
    }
    (args.out / "exclusion_inventory.json").write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
    with (args.out / "prior_report_headings.tsv").open("w") as out:
        out.write("packet\tsource\tline\theading\n")
        for p in packets:
            for narrative in p["primary_narratives"]:
                for h in narrative["headings"]:
                    out.write(f"{p['id']}\t{narrative['source']}\t{h['line']}\t{h['text']}\n")
    print(json.dumps({"coverage": data["coverage"], "term_hit_counts": {k: len(v) for k, v in hits.items()}}, indent=2))


if __name__ == "__main__":
    main()
