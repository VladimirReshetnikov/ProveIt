#!/usr/bin/env python3
"""Finite, exact source-checkpoint trace; it makes no TM-equivalence claim.

The input graph is the JSON already bound to p215 in the checked affine-core
packet.  A positive self-loop Test r is accelerated only when it does not add
to r: q positive branches followed by one zero branch, where q = R[r].
All other tests execute once.  Counts are source *checkpoint* transitions,
not individual source instructions and not binary-TM transitions.
"""
import argparse
from collections import deque
import hashlib
import json
from pathlib import Path
import time

GRAPH_SHA256 = "1bb3dbf084ef69d4c0464381afd200bb8ac3330d521890697344c6c8e0bbf0c3"
TARGETS = (4578, 4572, 4560)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--graph", type=Path, default=Path(__file__).parent / "drain_kernel/input_graph.json")
    ap.add_argument("--out", type=Path, default=Path(__file__).parent / "reachability_probe.json")
    ap.add_argument("--edges", type=int, default=100_000)
    ap.add_argument("--max-bits", type=int, default=4096)
    args = ap.parse_args()
    blob = args.graph.read_bytes()
    actual_hash = hashlib.sha256(blob).hexdigest()
    assert actual_hash == GRAPH_SHA256, (actual_hash, GRAPH_SHA256)
    graph = {int(k): v for k, v in json.loads(blob).items()}
    assert len(graph) == 1426
    for v, obj in graph.items():
        assert obj["op"][0] in ("halt", "decnz")
        for dest, additions in obj["successors"]:
            assert dest in graph
            for r, n in additions:
                assert 0 <= r < 9 and isinstance(n, int) and n >= 0

    vertex, regs = 25, [4, 0, 0, 0, 0, 0, 0, 0, 0]
    checkpoint_steps = ordinary_steps = drain_macros = accelerated = 0
    visited = set()
    seen_targets = {}
    prior = deque(maxlen=12)
    periodic = []
    chain = hashlib.sha256()
    max_reg_bits = 3
    started = time.monotonic()

    def state():
        return {"accelerated_edges": accelerated,
                "checkpoint_steps": checkpoint_steps,
                "vertex": vertex, "registers": list(regs)}

    while True:
        cur = state()
        chain.update((json.dumps(cur, sort_keys=True, separators=(",", ":")) + "\n").encode())
        visited.add(vertex)
        if vertex in TARGETS and vertex not in seen_targets:
            seen_targets[vertex] = {"state": cur, "preceding_states": list(prior)}
            print("HIT", json.dumps(cur, sort_keys=True), flush=True)
        if accelerated % 1000 == 0:
            periodic.append(cur)
        prior.append(cur)
        if len(seen_targets) == len(TARGETS):
            termination = "all_targets_reached"
            break
        if accelerated >= args.edges:
            termination = "accelerated_edge_limit"
            break
        if max(x.bit_length() for x in regs) > args.max_bits:
            termination = "register_bit_limit"
            break
        obj = graph[vertex]
        if obj["op"][0] == "halt":
            termination = "halt_node"
            break
        assert obj["op"][0] == "decnz" and len(obj["successors"]) == 2
        r = obj["op"][1]
        assert 0 <= r < 9
        (nz_dest, nz_adds), (z_dest, z_adds) = obj["successors"]
        if nz_dest == vertex and sum(n for i, n in nz_adds if i == r) == 0:
            q = regs[r]
            regs[r] = 0
            for i, n in nz_adds:
                regs[i] += q * n
            for i, n in z_adds:
                regs[i] += n
            checkpoint_steps += q + 1
            drain_macros += 1
            vertex = z_dest
        else:
            positive = regs[r] > 0
            if positive:
                regs[r] -= 1
            vertex, additions = obj["successors"][0 if positive else 1]
            for i, n in additions:
                regs[i] += n
            checkpoint_steps += 1
            ordinary_steps += 1
        accelerated += 1
        max_reg_bits = max(max_reg_bits, max(x.bit_length() for x in regs))

    receipt = {
        "kind": "finite_source_checkpoint_reachability_experiment",
        "graph_sha256": actual_hash,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "initial": {"vertex": 25, "registers": [4, 0, 0, 0, 0, 0, 0, 0, 0]},
        "supplied_initial_tm_frame": {"source_leaf": "1101001000", "tm_steps": 79633,
            "status": "supplied by state-reduction experiment; not checked by this script"},
        "targets": list(TARGETS), "limits": {"accelerated_edges": args.edges,
            "register_bits": args.max_bits},
        "termination": termination, "final": state(),
        "counts": {"drain_macros": drain_macros, "ordinary_checkpoint_steps": ordinary_steps,
            "visited_vertices": len(visited), "maximum_observed_register_bits": max_reg_bits},
        "first_hits": seen_targets, "periodic_states": periodic,
        "last_states": list(prior), "visited_vertices": sorted(visited),
        "trace_sha256": chain.hexdigest(), "elapsed_seconds": time.monotonic() - started,
        "scope": "Exact arithmetic trace of the supplied graph from the supplied initial state. "
                 "No claim of candidate blank-tape equivalence or of binary-TM transition counts. "
                 "Missing targets before the bound are not proved unreachable.",
    }
    args.out.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: receipt[k] for k in ("termination", "final", "counts", "trace_sha256", "elapsed_seconds")}, indent=2))
    print("receipt", args.out)


if __name__ == "__main__":
    main()
