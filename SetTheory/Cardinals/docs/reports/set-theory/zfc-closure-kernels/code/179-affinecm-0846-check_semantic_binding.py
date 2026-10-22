#!/usr/bin/env python3
"""Finite literal-address classification; inherited totality is cited, not re-proved."""
import argparse
import hashlib
import json
from pathlib import Path
import re


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--leaves", type=Path, required=True)
    ap.add_argument("--dag", type=Path, required=True)
    ap.add_argument("--graph", type=Path, required=True)
    ap.add_argument("--out", type=Path, default=Path(__file__).parent / "semantic_binding.json")
    args = ap.parse_args()
    leaves_raw = args.leaves.read_bytes()
    dag_raw = args.dag.read_bytes()
    graph_raw = args.graph.read_bytes()
    assert hashlib.sha256(leaves_raw).hexdigest() == "98da5d512f57c8be730f20c22778e805796622e6ea9fef1d5551567e87f1e9df"
    assert hashlib.sha256(dag_raw).hexdigest() == "ba2b28487ae978bd27b0d804e9b2bde6d9adcd1dd575de55572465c050b86aa1"
    assert hashlib.sha256(graph_raw).hexdigest() == "1bb3dbf084ef69d4c0464381afd200bb8ac3330d521890697344c6c8e0bbf0c3"
    graph = json.loads(graph_raw)
    gate_checkpoints = {
        4556: {"op": ["decnz", 3], "successors": [[4556, [[6, 1], [7, 1]]], [4560, []]]},
        4560: {"op": ["decnz", 5], "successors": [[4561, []], [4564, []]]},
        4564: {"op": ["decnz", 6], "successors": [[4565, []], [4570, []]]},
        4570: {"op": ["decnz", 1], "successors": [[4570, []], [4572, []]]},
        4572: {"op": ["decnz", 7], "successors": [[4572, [[6, 1]]], [4575, []]]},
        4575: {"op": ["decnz", 4], "successors": [[4575, [[5, 1]]], [4578, []]]},
    }
    for v, obj in gate_checkpoints.items():
        assert graph[str(v)] == obj
    leaves = json.loads(leaves_raw)
    nodes = {int(n): ((a, int(x) if x else None), (b, int(y) if y else None))
             for n, a, x, b, y in re.findall(
                 r"\| (\d+) => \((E\w+)(?: (\d+))?, (E\w+)(?: (\d+))?\)", dag_raw.decode())}
    gate = {457: (192, 458), 458: (131, 459), 459: (211, 460), 460: (197, 131)}
    for n, (a, b) in gate.items():
        assert nodes[n] == (("ENode", a), ("ENode", b))
    records = []
    for index, reg in ((26, 1), (4556, 3), (4560, 5), (4572, 7), (4578, 5)):
        source_path, source_op = leaves["source"][index]
        reference_path, reference_op = leaves["reference"][index]
        assert source_op == reference_op == ["decnz", reg]
        edge, ancestry = ("ENode", 0), []
        for k, bit in enumerate(reference_path):
            assert edge[0] == "ENode"
            ancestry.append({"node": edge[1], "prefix": reference_path[:k]})
            edge = nodes[edge[1]][int(bit)]
        assert edge == ("EDecnz", reg)
        ax_root = next(x for x in ancestry if x["node"] == 236)
        record = {"source_index": index, "source_path": source_path,
                  "reference_path": reference_path, "operation": source_op,
                  "AX_root_prefix": ax_root["prefix"], "ancestor_nodes": [x["node"] for x in ancestry]}
        if index == 26:
            assert set(reference_path[len(ax_root["prefix"]):]) <= {"0"}
            record["classification"] = "first primitive of AX node236"
        else:
            gate_root = next(x for x in ancestry if x["node"] == 457)
            suffix = reference_path[len(gate_root["prefix"]):]
            assert suffix == {4556: "00", 4560: "100000", 4572: "1100", 4578: "11110000"}[index]
            record["gate_prefix"] = gate_root["prefix"]
            record["gate_suffix"] = suffix
            record["classification"] = {4556: "first primitive of final gate node457",
                                        4560: "first ifeq_clear: compare c against B",
                                        4572: "loop211: move saved c from scratch7 to scratch6",
                                        4578: "second ifeq_clear: compare c against A"}[index]
        records.append(record)
    assert len({x["gate_prefix"] for x in records[1:]}) == 1
    result = {"kind": "literal_source_controls_classified",
              "leaves_sha256": hashlib.sha256(leaves_raw).hexdigest(),
              "dag_sha256": hashlib.sha256(dag_raw).hexdigest(),
              "graph_sha256": hashlib.sha256(graph_raw).hexdigest(),
              "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "gate_nodes": gate, "gate_checkpoints": gate_checkpoints, "controls": records,
              "scope": "Finite literal-binding check only. Eventual visitation additionally uses the "
                       "existing total AX macro-run theorems and the direct180-step entry prefix, "
                       "as explained in README. No new kernel reachability theorem is claimed."}
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    print("Literal AX entry and allthree final-gate controls matched.")


if __name__ == "__main__":
    main()
