#!/usr/bin/env python3
"""Direct checkpoint replay, deliberately without drain acceleration."""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--graph", type=Path, required=True)
    ap.add_argument("--receipt", type=Path, default=Path(__file__).parent / "reachability_probe.json")
    ap.add_argument("--out", type=Path, default=Path(__file__).parent / "direct_replay.json")
    args = ap.parse_args()
    blob = args.graph.read_bytes()
    graph_hash = hashlib.sha256(blob).hexdigest()
    assert graph_hash == "1bb3dbf084ef69d4c0464381afd200bb8ac3330d521890697344c6c8e0bbf0c3"
    graph = {int(v): x for v, x in json.loads(blob).items()}
    receipt = json.loads(args.receipt.read_text())
    expected = {x["checkpoint_steps"]: x for x in receipt["periodic_states"][:11]}
    vertex, regs = 25, [4, 0, 0, 0, 0, 0, 0, 0, 0]
    matches, first_ax, prefix = [], None, []
    for steps in range(max(expected) + 1):
        state = {"checkpoint_steps": steps, "vertex": vertex, "registers": regs.copy()}
        if first_ax is None:
            prefix.append(state)
            if vertex == 26:
                first_ax = state
        if steps in expected:
            target = expected[steps]
            assert vertex == target["vertex"] and regs == target["registers"], (state, target)
            matches.append(steps)
        if steps == max(expected):
            break
        obj = graph[vertex]
        assert obj["op"][0] == "decnz"
        r = obj["op"][1]
        positive = regs[r] > 0
        if positive:
            regs[r] -= 1
        vertex, additions = obj["successors"][0 if positive else 1]
        for i, n in additions:
            regs[i] += n
    assert first_ax == {"checkpoint_steps": 180, "vertex": 26,
                        "registers": [7, 0, 0, 0, 0, 0, 0, 0, 0]}
    result = {"kind": "independent_direct_checkpoint_replay", "graph_sha256": graph_hash,
              "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "receipt_sha256": hashlib.sha256(args.receipt.read_bytes()).hexdigest(),
              "matched_checkpoint_steps": matches, "first_AX_entry": first_ax,
              "initial_prefix": prefix,
              "scope": "Direct finite execution of the source checkpoint graph. "
                       "No drain acceleration, binary-TM simulation, or proof-assistant invocation."}
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    print("Direct replay passed; AX entry at180;11 checkpoints matched through31323 steps.")


if __name__ == "__main__":
    main()
