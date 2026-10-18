#!/usr/bin/env python3
"""Independent phase-mask and move-boundary checks for role allocation.

Reads the original extracted literal source graph and candidate annotations.
It intentionally implements mask transfer separately from dynamic_renaming.
The source-graph-to-Lean decoder calibration is inherited as a separate gate.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib
import json
from pathlib import Path
import sys


def main() -> None:
    if not __debug__:
        raise SystemExit("run with assertions enabled")
    ap = argparse.ArgumentParser()
    ap.add_argument("--candidate-dir", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    sys.path.insert(0, str(args.candidate_dir))
    d = importlib.import_module("dynamic_renaming")
    K = 32

    def transfer(vector, case):
        if vector is None or any(x == 0 for x in vector):
            return None
        site, path, op, r, zero_branch = case
        del site, path
        out = list(vector)
        if op == "CI":
            out[r] = 0
            for value in range(K + 1):
                if vector[r] & (1 << value):
                    out[r] |= 1 << min(K, value + 1)
        elif op == "CD":
            if zero_branch:
                if not vector[r] & 1:
                    return None
                out[r] = 1
            else:
                out[r] = 0
                for value in range(1, K + 1):
                    if vector[r] & (1 << value):
                        out[r] |= 1 << (value - 1)
                        if value == K:
                            out[r] |= 1 << K
                if out[r] == 0:
                    return None
        else:
            assert op in {"CB", "CC", "CH"}
        return tuple(out)

    assert len(d.values) == len(d.sites) == 6460
    # The compiler consumes the shared decoder DAG, whereas the masks consume
    # the unfolded literal source. Compare all leaves of those two inputs.
    decoder_leaves = {}
    unfolded_nodes = 0

    def unfold(node, path, active):
        nonlocal unfolded_nodes
        assert node not in active, ("cyclic_source_DAG", node)
        pair = d.dag["nodes"][str(node)]
        assert len(pair) == 2
        unfolded_nodes += 1
        for bit, edge in enumerate(pair):
            target_path = path + str(bit)
            if edge[0] == "N":
                unfold(edge[1], target_path, active | {node})
            else:
                assert edge[0] in {"I", "D", "B", "C", "H"}
                decoder_leaves[target_path] = (
                    "C" + edge[0], edge[1] if len(edge) == 2 else None
                )

    unfold(d.dag["root"], "", frozenset())
    assert decoder_leaves == {path: (op, operand) for path, op, operand in d.sites}
    assert unfolded_nodes == 6459
    assert all(mask & 1 for mask in d.values[d.first])
    live = dead = halts = 0
    for ci, case in enumerate(d.cases):
        site = case[0]
        post = transfer(d.values[site], case)
        assert post == d.transfer(d.values[site], ci)
        if post is None:
            dead += 1
            continue
        live += 1
        dst = d.targets[ci]
        if dst is None:
            assert case[2] == "CH"
            halts += 1
        else:
            assert case[2] != "CH"
            assert d.values[dst] is not None
            assert all(a & ~b == 0 for a, b in zip(post, d.values[dst])), (ci, post, d.values[dst])

    records = []
    for occ in d.occurrences:
        path = occ["path"]
        header = d.lookup[path + "0"]
        body = d.lookup[path + "10"]
        back = d.lookup[path + "11"]
        source, dest = occ["source"], occ["destination"]
        assert source != dest
        assert header == occ["site"]
        zero_cases = [ci for ci in d.by[header] if d.cases[ci][4] is True]
        positive_cases = [ci for ci in d.by[header] if d.cases[ci][4] is False]
        assert len(zero_cases) == len(positive_cases) == 1
        z, p = zero_cases[0], positive_cases[0]
        assert d.cases[z][2:4] == d.cases[p][2:4] == ("CD", source)
        assert len(d.by[body]) == len(d.by[back]) == 1
        inc, cont = d.by[body][0], d.by[back][0]
        assert d.cases[inc][2:4] == ("CI", dest)
        assert d.cases[cont][2:4] == ("CC", 2)
        assert d.targets[p] == body and d.targets[inc] == back and d.targets[cont] == header
        assert set(d.incoming[body]) == {p}
        assert set(d.incoming[back]) == {inc}
        external = [ci for ci in d.incoming[header] if ci != cont]
        assert set(external) == set(occ["external"])
        entry = [0] * 9
        for ci in external:
            post = transfer(d.values[d.cases[ci][0]], d.cases[ci])
            if post is not None:
                entry = [a | b for a, b in zip(entry, post)]
        assert tuple(entry) == tuple(occ["entry_masks"])
        assert occ["accepted"] == (entry[dest] == 1)
        if occ["accepted"]:
            expected_exit = d.targets[z]
            assert d.swaps[header] == (source, dest, expected_exit)
            macro_post = entry.copy()
            macro_post[dest], macro_post[source] = entry[source], 1
            target_masks = d.entry_values.get(expected_exit, d.values[expected_exit])
            assert target_masks is not None
            assert all(a & ~b == 0 for a, b in zip(macro_post, target_masks)), (header, expected_exit)
        records.append({"site": header, "path": path, "source": source, "destination": dest,
                        "zero_exit": d.targets[z], "external_predecessors": len(external),
                        "zero_destination_certified": occ["accepted"]})

    source_files = ["dynamic_renaming.py", "value-analysis-32.json", "input/Prog254.v",
                    "input/permutation252_phase_analysis.py",
                    "input/27-variant-experiments-machine_search-grammar_search-decoder_entries.json"]
    out = {"status": "PASS independent mask closure and exact move boundaries",
           "mask_classes": "0,...,31,>=32", "sites": len(d.sites),
           "shared_decoder_nodes": len(d.dag["nodes"]),
           "unfolded_decoder_nodes": unfolded_nodes,
           "all_decoder_leaves_match_literal_source": True,
           "cases": len(d.cases), "feasible_cases": live, "infeasible_cases": dead,
           "actual_halt_cases": halts, "initial_all_zero_vector_included": True,
           "mask_transfer_inclusions_checked": live - halts,
           "move_occurrences": len(records),
           "accepted_zero_destination_moves": sum(x["zero_destination_certified"] for x in records),
           "all_sources_destinations_distinct": True,
           "no_external_entries_to_move_interiors": True,
           "macro_exits_equal_literal_zero_branch_targets": True,
           "macro_postconditions_in_target_masks": True,
           "source_sha256": {name: hashlib.sha256((args.candidate_dir / name).read_bytes()).hexdigest()
                             for name in source_files},
           "records": records}
    args.output.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({k: v for k, v in out.items() if k not in {"source_sha256", "records"}}, indent=2))


if __name__ == "__main__":
    main()
