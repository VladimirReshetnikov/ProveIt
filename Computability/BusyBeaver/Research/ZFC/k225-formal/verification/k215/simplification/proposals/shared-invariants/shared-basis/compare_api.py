#!/usr/bin/env python3
"""Static public-interface comparison for the two shared-basis proposal files.

This is a scoped source scanner, not a Lean parser or elaborated type check.
It compares conventional unindented public declaration headers, and separately
checks exact byte equality of the relevant definition blocks and Tarski tail.
No compilation, network access, or repository mutation is performed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


def digest(data):
    return hashlib.sha256(data).hexdigest()


def declarations(text):
    result = {}
    namespace = ""
    pattern = re.compile(
        r"(?m)^(?:namespace\s+([^\s]+)|"
        r"(?:(?:noncomputable|protected)\s+)?"
        r"(theorem|def|abbrev|structure|inductive|class)\s+([\w.']+))")
    for match in pattern.finditer(text):
        if match.group(1):
            namespace = match.group(1)
            continue
        start = match.start()
        # These specific files use := or where as the declaration delimiter.
        end = re.search(r":=|\bwhere\b", text[match.end():])
        if end is None:
            raise ValueError(f"No declaration delimiter for {match.group(3)}")
        header = text[start:match.end() + end.start()].strip()
        name = namespace + "." + match.group(3)
        if name in result:
            raise ValueError(f"Duplicate public name: {name}")
        result[name] = {"header": header,
                        "normalized_header": re.sub(r"\s+", " ", header)}
    return result


def block(text, start, end=None):
    first = text.index(start)
    last = len(text) if end is None else text.index(end, first)
    return text[first:last].encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, required=True,
                        help="Pinned original BusyBeaver/ZFC directory")
    parser.add_argument("--proposal", type=Path, required=True,
                        help="Proposed BusyBeaver/ZFC directory")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    files, block_results = {}, []
    for stem in ["DominatedImplication", "Lukasiewicz"]:
        old_path = args.baseline / (stem + ".lean")
        new_path = args.proposal / (stem + ".lean")
        old_bytes, new_bytes = old_path.read_bytes(), new_path.read_bytes()
        old, new = old_bytes.decode("utf-8"), new_bytes.decode("utf-8")
        old_decls, new_decls = declarations(old), declarations(new)
        common = sorted(old_decls.keys() & new_decls.keys())
        comparisons = []
        for name in common:
            a, b = old_decls[name], new_decls[name]
            comparisons.append({"name": name, "baseline_header": a["header"],
                                "proposal_header": b["header"],
                                "exact_header_equal": a["header"] == b["header"],
                                "whitespace_normalized_header_equal":
                                a["normalized_header"] == b["normalized_header"]})
        files[stem] = {
            "baseline_path": str(old_path.resolve()),
            "proposal_path": str(new_path.resolve()),
            "baseline_sha256": digest(old_bytes), "proposal_sha256": digest(new_bytes),
            "removed_public_names": sorted(old_decls.keys() - new_decls.keys()),
            "added_public_names": sorted(new_decls.keys() - old_decls.keys()),
            "common_public_declarations": comparisons,
        }
        specs = ([('Language, rho8 and Restricted definitions', 'structure Language', '\nsection')]
                 if stem == "DominatedImplication" else
                 [('Implicational definition', 'structure Implicational', '\nvariable {imp'),
                  ('Entire Tarski namespace tail',
                   'namespace SetTheory.BusyBeaver.ZFC.Tarski', None)])
        for label, start, end in specs:
            a, b = block(old, start, end), block(new, start, end)
            block_results.append({"file": stem + ".lean", "block": label,
                                  "start_marker": start, "end_marker": end,
                                  "baseline_bytes": len(a), "proposal_bytes": len(b),
                                  "baseline_sha256": digest(a), "proposal_sha256": digest(b),
                                  "exact_byte_equal": a == b})
    passed = all(not x["removed_public_names"] and
                 all(d["whitespace_normalized_header_equal"]
                     for d in x["common_public_declarations"]) for x in files.values())
    passed = passed and all(b["exact_byte_equal"] for b in block_results)
    report = {
        "baseline_commit": "57541fe0cfe3af62b4cb58747d8d1d7c16b338d5",
        "proposal_origin_commit": "49e99c5b7cc6c2e164331961de28bad3904361fd",
        "method": "Scoped source-header comparison plus exact byte-block comparisons",
        "scope": "No compilation or elaborated-type equivalence claimed. Private derivation bodies intentionally change.",
        "files": files, "exact_blocks": block_results, "passed": passed,
    }
    args.out.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"passed": passed, "output": str(args.out),
                      "common_declarations": sum(len(x["common_public_declarations"])
                                                 for x in files.values()),
                      "exact_blocks": len(block_results)}))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
