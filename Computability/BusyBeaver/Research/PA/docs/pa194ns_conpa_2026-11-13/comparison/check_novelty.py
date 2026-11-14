#!/usr/bin/env python3
"""Exact graph comparison against every 194-state literal table in the census.

Usage: python3 check_novelty.py candidate.tm [--census census/census.json]

The prior table bytes must be in <census-directory>/tables/<sha256>.tm.
For every graph-spanning root we assign breadth-first labels in read-bit order.
This canonical representation is exact for rooted deterministic action graphs.
Taking its minimum over all roots, both reflections, and both global bit
exchanges removes those cosmetic choices. Equality is checked on tuples, not
only on their digests. A positive novelty result says nothing about correctness
of the candidate's arithmetic or operational semantics.
"""
from pathlib import Path
import argparse
import hashlib
import json

from census import canonical, parse_table


def digest(data):
    return hashlib.sha256(data).hexdigest()


def all_cosmetic_form(table):
    best = None
    root_count = 0
    for reflected in (False, True):
        for exchanged in (False, True):
            for root in sorted(table[1]):
                form = canonical(table, root, reflected, exchanged)
                if form is not None:
                    root_count += 1
                    if best is None or form < best:
                        best = form
    if best is None:
        raise ValueError("No working state reaches the entire action graph")
    return best, root_count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--census", type=Path,
                        default=Path(__file__).parent / "census/census.json")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    corpus = json.loads(args.census.read_text())
    candidate_bytes = args.candidate.read_bytes()
    candidate = parse_table(candidate_bytes)
    if candidate is None:
        raise ValueError("Candidate is not a complete numeric binary table")
    candidate_form, roots = all_cosmetic_form(candidate)
    records = [x for x in corpus["identities"]
               if x["states"] == len(candidate[1])]
    matches = []
    for record in records:
        path = args.census.parent / "tables" / (record["sha256"] + ".tm")
        prior_bytes = path.read_bytes()
        if digest(prior_bytes) != record["sha256"]:
            raise ValueError("Changed prior table: " + str(path))
        prior = parse_table(prior_bytes)
        if prior is None or len(prior[1]) != record["states"]:
            raise ValueError("Invalid prior table: " + str(path))
        prior_form, _ = all_cosmetic_form(prior)
        if prior_form == candidate_form:
            matches.append({"sha256": record["sha256"],
                            "first_path": record["first_path"]})
    result = {
        "candidate_sha256": digest(candidate_bytes),
        "working_states": len(candidate[1]),
        "transition_rows": len(candidate[0]),
        "transformed_spanning_roots": roots,
        "candidate_cosmetic_hash": digest(repr(candidate_form).encode()),
        "comparison_snapshot": corpus["snapshot"],
        "prior_table_byte_forms": len(records),
        "prior_action_graph_classes": len({x["graph_hash"] for x in records}),
        "matches": matches,
        "result": "MATCH" if matches else "NOVEL",
        "scope": "State renaming; all graph-spanning roots; tape reflection; "
                 "global simultaneous read/write bit exchange. Exact tuple "
                 "comparison, with SHA-256 only for input integrity."
    }
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
