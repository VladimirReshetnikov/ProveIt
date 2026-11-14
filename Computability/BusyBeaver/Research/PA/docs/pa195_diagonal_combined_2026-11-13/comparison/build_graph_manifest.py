#!/usr/bin/env python3
"""Build compact graph-class provenance from census.py/graph_census.py output."""
from pathlib import Path
import argparse
import collections
import csv
import json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("census_directory", type=Path)
    parser.add_argument("output_directory", type=Path)
    args = parser.parse_args()
    summary = json.loads((args.census_directory / "summary.json").read_text())
    tables = json.loads((args.census_directory / "tables.json").read_text())
    graphs = json.loads((args.census_directory / "root_free_graphs.json").read_text())
    by_table = collections.defaultdict(list)
    for table in tables:
        if "transition_sha256" in table:
            by_table[table["transition_sha256"]].append(table)
    by_graph = collections.defaultdict(list)
    for graph in graphs:
        by_graph[graph["root_free_graph_sha256"]].append(graph)
    classes = []
    for digest, group in sorted(by_graph.items(), key=lambda item: (item[1][0]["working_states"], item[0])):
        encodings = []
        for graph in group:
            occurrences = by_table[graph["transition_sha256"]]
            encodings.append({
                "transition_sha256": graph["transition_sha256"],
                "raw_sha256s": sorted({table["raw_sha256"] for table in occurrences}),
                "canonicalizing_root_label": graph["canonicalizing_root_label"],
                "occurrences": [
                    {key: table[key] for key in ("source", "member", "archive_sha256")}
                    for table in occurrences
                ],
            })
        classes.append({
            "working_states": group[0]["working_states"],
            "root_free_graph_sha256": digest,
            "table_occurrences": sum(len(encoding["occurrences"]) for encoding in encodings),
            "labeled_transition_functions": len(encodings),
            "encodings": encodings,
        })
    manifest = {
        "repository": "VladimirReshetnikov/ProveIt",
        "commit": summary["commit"],
        "canonicalization": "minimum BFS action word over working roots reaching every working state; bit0 edge before bit1; all terminal controls map to -1; JSON compact separators; SHA256",
        "classes": classes,
        "scope": "Literal numeric binary tables in the pinned PA tree and incoming archives, recursively. Includes diagnostics, ancestors and synthetic controls. Root-free graph identity ignores the intended start. Two disconnected synthetic controls are listed separately.",
    }
    args.output_directory.mkdir(parents=True, exist_ok=True)
    (args.output_directory / "graph_classes.json").write_text(json.dumps(manifest, indent=2) + "\n")
    fields = ["working_states", "root_free_graph_sha256", "table_occurrences", "labeled_transition_functions", "representative_source", "representative_member"]
    with (args.output_directory / "graph_classes.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        for graph in classes:
            origin = graph["encodings"][0]["occurrences"][0]
            writer.writerow({key: graph[key] for key in fields[:4]} | {
                "representative_source": origin["source"],
                "representative_member": origin["member"],
            })
    print(json.dumps({"graph_classes": len(classes), "commit": summary["commit"]}, indent=2))


if __name__ == "__main__":
    main()
