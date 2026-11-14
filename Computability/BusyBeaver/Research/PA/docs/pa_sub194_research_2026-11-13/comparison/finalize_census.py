#!/usr/bin/env python3
"""Group recomputed literal occurrences; behavior/calibration statuses are inherited.

The imported classifier is exact up to control renaming for the one-halt tables
with a spanning root used in the main census. Its nonspanning diagnostic keys
are not claimed to solve unrestricted disconnected-graph isomorphism.
"""
from pathlib import Path
import argparse
import collections
import csv
import json

PIN = "5784600f8709872fa258af66a94df8deb7075c2f"


def finalize(directory):
    directory = Path(directory)
    rows = json.loads((directory / "table_occurrences.json").read_text())
    grouped = {}
    for row in rows:
        grouped.setdefault(row["table"], []).append(row)
    classes = []
    for key, members in grouped.items():
        representative = min(members, key=lambda row: (
            row["origin"] != "PA_direct", len(row["path"]), row["path"]))
        maximum = max(row.get("max_reachable", row["reachable"]) for row in members)
        classes.append(dict(graph_class=key, working_states=representative["states"],
            max_reachable_states=maximum,
            has_spanning_root=maximum == representative["states"],
            halt_targets=representative["halting"], occurrences=len(members),
            byte_forms=len({row["sha256"] for row in members}),
            representative=representative["path"], paths=[row["path"] for row in members]))
    classes.sort(key=lambda record: (record["working_states"], record["graph_class"]))
    valid = [record for record in classes
             if record["has_spanning_root"] and len(record["halt_targets"]) == 1]
    old = {row["table"] for row in rows if row["origin"] == "PA_direct"}
    new = [record for record in classes if record["graph_class"] not in old]
    summary = dict(snapshot=PIN,
        scope="Direct PA .tm files; numeric .tm/.txt/.csv/.tsv members of recursive PA/incoming ZIPs, each distinct ZIP body once. JSON/code embedded encodings are outside this literal census.",
        comparison="Control renaming with symbols and L/R preserved; any spanning root. Starts are not identified behaviorally. Nonspanning diagnostics use classifier keys only.",
        files_scanned=dict(literal_table_occurrences=len(rows),
            distinct_bytes=len({row["sha256"] for row in rows}),
            PA_direct_occurrences=sum(row["origin"] == "PA_direct" for row in rows),
            PA_nested_archive_occurrences=sum(row["origin"] == "PA_nested_archive" for row in rows),
            incoming_occurrences=sum(row["origin"] == "incoming" for row in rows)),
        distinct_graph_classes=len(classes),
        spanning_one_halt_graph_classes=len(valid),
        spanning_one_halt_classes_by_working_states=dict(sorted(collections.Counter(
            record["working_states"] for record in valid).items())),
        **{"194_state_graph_classes": sum(record["working_states"] == 194 for record in valid)},
        new_graph_classes_in_incoming=len(new),
        new_194_graph_classes_in_incoming=sum(record["working_states"] == 194 for record in new),
        rejected_194_new_graphs=1, proposed_194_new_graphs=7,
        diagnostic_classes_excluded=[record for record in classes
            if not record["has_spanning_root"] or len(record["halt_targets"]) != 1],
        warning="Counts/graph distinctions are recomputed. The seven proposed and one rejected incoming194 statuses are report-derived at the fixed snapshot. No Con(PA) calibration or state minimum is verified by this census.")
    for name, value in (("census_summary.json", summary), ("machine_classes.json", classes),
                        ("incoming_new_classes.json", new)):
        (directory / name).write_text(json.dumps(value, indent=2) + "\n")
    with (directory / "graph_class_inventory.csv").open("w", newline="") as handle:
        columns = ["graph_class", "working_states", "has_spanning_root", "occurrences",
                   "byte_forms", "representative"]
        writer = csv.DictWriter(handle, fieldnames=columns)
        writer.writeheader()
        writer.writerows({key: record[key] for key in columns} for record in classes)
    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    result = finalize(args.directory)
    print(json.dumps({key: value for key, value in result.items()
                      if key != "diagnostic_classes_excluded"}, indent=2))
