#!/usr/bin/env python3
"""Reproduce the complete 37-presentation, 30-class supplied-design catalogue."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "comparison_audit", ROOT / "comparison/comparison/compare_designs.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


def catalogue():
    inp = ROOT / "comparison/comparison/inputs"
    manifest = json.loads((inp / "manifest.json").read_text())
    layouts = json.loads((ROOT / "comparison/accepted196/manifest.json").read_text())
    entries = []
    for item in manifest["tables"]:
        entries.append({
            "id": item["id"],
            "file": str((inp / item["file"]).relative_to(ROOT)),
            "sha256": item["sha256"],
            "origin_archive": item.get("archive"),
            "origin_member": item.get("member"),
        })
    known = {entry["sha256"] for entry in entries}
    names = {2: "pa196_factorization_scanner", 3: "pa196_close_cd6",
             4: "pa196_close_cd3", 5: "pa196_close_cd5", 6: "pa196_close_cd4",
             7: "pa196_rotated", 8: "pa196_rotated_macro62"}
    for index, item in enumerate(layouts):
        if item["sha256"] in known:
            continue
        entries.append({
            "id": names[index],
            "file": "comparison/accepted196/" + item["file"],
            "sha256": item["sha256"],
            "origin_path": item["path"],
        })
        known.add(item["sha256"])
    classes = {}
    for entry in entries:
        raw = (ROOT / entry["file"]).read_bytes()
        audit.require(hashlib.sha256(raw).hexdigest() == entry["sha256"],
                      "Input hash mismatch: " + entry["id"])
        table, states, halt = audit.table(raw)
        canonical, order = audit.canonical(table, states, halt)
        key = json.dumps(canonical, separators=(",", ":"))
        if key not in classes:
            classes[key] = "C" + str(len(classes)).zfill(2)
        entry.update(states=len(states), halt_label=halt,
                     rooted_action_graph_class=classes[key],
                     canonical_graph_sha256=hashlib.sha256(key.encode()).hexdigest())
    audit.require(len(entries) == 37 and len(classes) == 30, "Unexpected census")
    return {"scope": "Supplied accepted presentations; excludes new constructions",
            "states_exclude_halt": True, "presentations": 37, "rooted_classes": 30,
            "source_pins": {"PA196": "407cdc356f6b586635e71ac92be394255f4bfea4",
                            "PA209": "69d98241a721ead20b4f0b17df9062950b40fbfe",
                            "ProveIt": "dc523e7b06ffb414093c90aa035500ca283e5f75"},
            "entries": entries}


def tex(data):
    lines = [r"\clearpage", r"\section{Complete supplied-design catalogue}",
             r"The identifiers below match the comparison artifacts. Classes preserve the",
             r"initial state, halt, read/write symbols, and move directions. The abbreviated",
             r"hash column is for navigation only; \code{catalogue.json} records complete",
             r"SHA-256 values, original archive members, and exact local table paths.",
             r"This catalogue excludes the new constructions of Section~\ref{sec:constructions}.",
             r"\small", r"\begin{longtable}{lrrl}", r"\toprule",
             r"Presentation & States & Class & SHA-256 prefix\\", r"\midrule",
             r"\endfirsthead", r"\toprule",
             r"Presentation & States & Class & SHA-256 prefix\\", r"\midrule",
             r"\endhead", r"\bottomrule", r"\endfoot"]
    for entry in data["entries"]:
        lines.append(r"\code{" + entry["id"] + "} & " + str(entry["states"]) +
                     " & " + entry["rooted_action_graph_class"] + r" & \code{" +
                     entry["sha256"][:14] + r"}\\")
    lines.extend([r"\end{longtable}", r"\normalsize"])
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tex", type=Path)
    args = parser.parse_args()
    data = catalogue()
    (ROOT / "catalogue.json").write_text(json.dumps(data, indent=2) + "\n")
    if args.tex:
        args.tex.write_text(tex(data))
    print("PASS: 37 supplied presentations in 30 rooted action-graph classes")
