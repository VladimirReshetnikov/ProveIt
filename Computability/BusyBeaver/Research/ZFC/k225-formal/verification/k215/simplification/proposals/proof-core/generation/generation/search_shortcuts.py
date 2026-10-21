#!/usr/bin/env python3
"""Finite discovery search over the 117 pinned numbered helper schemas.
This is not an optimality proof. The delivered shortcuts are checked separately
by regenerate.py and the theorem itself by Lean/Rocq.
"""
import argparse, json
import regenerate as r

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", type=str, help="optional output of all schematic MP rewrites")
    args = ap.parse_args()
    ns = r.read_nodes((r.HERE / "DomRho8.original.lean").read_text())
    results = []
    for x in ns.values():
        if x["guarded"] or not isinstance(x["term"], tuple):
            continue
        for y in ns.values():
            if y["guarded"]:
                continue
            major, minor = r.renamed(x["term"], "x"), r.renamed(y["term"], "y")
            unifier = {}
            if not r.unify(major[0], minor, unifier):
                continue
            conclusion = r.substitute(major[1], unifier)
            for z in ns.values():
                if z["name"] in (x["name"], y["name"]):
                    continue
                instance = {}
                if r.match(conclusion, z["term"], instance):
                    results.append(dict(target=z["name"], major=x["name"], minor=y["name"]))
    chosen = json.loads((r.HERE / "shortcuts.json").read_text())["shortcuts"]
    assert all(c in results for c in chosen)
    if args.json:
        from pathlib import Path
        Path(args.json).write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps({
        "helper_schemas": len(ns),
        "ordered_single_mp_rewrites": len(results),
        "delivered_shortcuts": len(chosen),
        "all_delivered_shortcuts_in_search": True,
        "optimality_claim": False,
        "scope": "one condensed-detachment step between existing unconditional schemas",
    }, indent=2))

if __name__ == "__main__":
    main()
