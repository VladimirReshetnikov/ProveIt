#!/usr/bin/env python3
"""Literal rejection witness for deleting the globally shared g;m prefix.

The positive-loop drain is unreachable at one NIP occurrence, but is needed
in the other three uses of the shared comparison.  This is a register-source
counterexample; the separate binary audit identifies its four call sites.
"""
import hashlib
import json
from pathlib import Path
import formalism_dirty_seed as vm

ROOT = Path(__file__).resolve().parent


def main():
    old = vm.parse()
    assert old[127] == (("ENode", 207), ("EInc", 5))
    # Add a literal right-associated AX tail, without accelerated helper calls.
    old.update({219: (("ENode", 192), ("ENode", 220)),
                220: (("ENode", 131), ("ENode", 221)),
                221: (("ENode", 211), ("ENode", 222)),
                222: (("ENode", 197), ("ENode", 131))})
    changed = {n: tuple(("EInc", 5) if e == ("ENode", 127) else e for e in row)
               for n, row in old.items()}
    results = []
    for label, c, a, b in [("missed_collision", 2, 2, 0),
                            ("spurious_collision", 3, 5, 0),
                            ("missed_collision_and_dirty_scratch", 3, 3, 0)]:
        seed = [0, 4, 0, c, a, b, 0, 0, 0]
        entries = {}
        for name, nodes in [("original", old), ("shared_loop_deleted", changed)]:
            final1, trace1, calls, _ = vm.structured(nodes, seed, root=219)
            final2, trace2 = vm.flat_path(nodes, seed, root=219)
            assert final1 == final2 and trace1 == trace2
            entries[name] = {"final": final1, "structured_edge_calls": calls,
                             "primitive_events": len(trace1),
                             "two_literal_interpreters_agree": True}
        assert entries["original"]["final"] != entries["shared_loop_deleted"]["final"]
        assert entries["original"]["final"][1] == (4 if c != a and c != b else 0)
        results.append({"case": label, "c": c, "a": a, "b": b,
                        "initial": seed, **entries})
    result = {"status": "REJECTED_SHARED_DELETION",
              "witness_checks": "PASS",
              "scope": "AX gate source contract; not an assertion of actual blank-tape halting",
              "source_sha256": hashlib.sha256(vm.SOURCE.read_bytes()).hexdigest(),
              "original_tail": [192, 131, 211, 197, 131],
              "mutation": "Replace every call of node127=(node207,IncH) by IncH",
              "cases": results}
    path = ROOT / "formalism_shared_gate_counterexample.json"
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
