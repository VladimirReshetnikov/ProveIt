#!/usr/bin/env python3
"""Independent finite source bootstrap for the candidate deleting one loop.

This checks the original literal 219-node source, not the binary runtime.
The binary-to-source comparison must separately justify its guarded pruning.
Two interpreters (structured recursion and a flat path machine) agree on every
primitive event and the final register file; neither uses accelerated helpers.
"""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "formalism_reference" / "Dag254.v"
SEED = [3, 0, 0, 0, 3, 0, 35, 0, 0]
WANTED = [39, 0, 0, 0, 3, 0, 0, 0, 0]


def parse():
    nodes = {}
    for n, a, b in re.findall(
            r"\| ([0-9]+) => \((E\w+(?: [0-9]+)?), (E\w+(?: [0-9]+)?)\)",
            SOURCE.read_text()):
        def edge(s):
            parts = s.split()
            return (parts[0], int(parts[1])) if len(parts) == 2 else (parts[0],)
        nodes[int(n)] = edge(a), edge(b)
    assert len(nodes) == 219
    return nodes


def operation(edge, r):
    kind, *arg = edge
    if kind == "EHalt":
        return "halt", 0
    n = arg[0]
    if kind == "EInc":
        r[n] += 1
        return "normal", 0
    if kind == "EDecnz":
        if r[n]:
            r[n] -= 1
            return "normal", 0
        return "break", 1
    assert kind in ("EBreak", "EContinue")
    return ("break" if kind == "EBreak" else "continue"), n


def structured(nodes, seed, root=0):
    r, trace, calls, checkpoints = list(seed), [], 0, []

    def run(edge, path):
        nonlocal calls
        calls += 1
        assert calls < 10000
        if edge[0] != "ENode":
            before = list(r)
            result = operation(edge, r)
            trace.append({"path": path, "edge": list(edge), "before": before,
                          "after": list(r), "exit": list(result)})
            return result
        node = edge[1]
        before = list(r)
        while True:
            left, right = nodes[node]
            kind, k = run(left, path + "0")
            if kind == "break":
                result = ("normal", 0) if k == 1 else (kind, k - 1)
                break
            if kind != "normal":
                result = kind, k
                break
            kind, k = run(right, path + "1")
            if kind == "continue":
                if k == 1:
                    continue
                result = kind, k - 1
            else:
                result = kind, k
            break
        if node in (133, 174, 175, 141):
            checkpoints.append({"node": node, "before": before, "after": list(r),
                                "exit": list(result)})
        return result

    result = run(("ENode", root), "")
    assert result == ("normal", 0)
    return r, trace, calls, checkpoints


def flat_path(nodes, seed, root=0):
    """Path semantics: do not recurse through the execution control flow."""
    r, pc, trace = list(seed), "", []

    def advance(path):
        path = path.rstrip("1")
        return path[:-1] + "1" if path else None

    for _ in range(10000):
        edge, depth = ("ENode", root), 0
        while edge[0] == "ENode":
            bit = int(pc[depth]) if depth < len(pc) else 0
            edge = nodes[edge[1]][bit]
            depth += 1
        path = pc.ljust(depth, "0")
        before = list(r)
        # Independently execute the primitive, rather than calling operation().
        tag = edge[0]
        if tag == "EInc":
            r[edge[1]] += 1
            kind, k = "normal", 0
        elif tag == "EDecnz":
            if r[edge[1]] == 0:
                kind, k = "break", 1
            else:
                r[edge[1]] -= 1
                kind, k = "normal", 0
        elif tag in ("EBreak", "EContinue"):
            kind, k = ("break" if tag == "EBreak" else "continue"), edge[1]
        else:
            assert tag == "EHalt"
            kind, k = "halt", 0
        trace.append({"path": path, "edge": list(edge), "before": before,
                      "after": list(r), "exit": [kind, k]})
        assert kind != "halt", "unexpected source halt"
        if kind == "normal":
            pc = advance(path)
        else:
            target = "0" if kind == "break" else "1"
            while k and path:
                k -= path[-1] == target
                path = path[:-1]
            assert k == 0, "unexpected escaping break/continue"
            pc = advance(path) if kind == "break" else path
        if pc is None:
            return r, trace
    raise AssertionError("flat path fuel exhausted")


def main():
    nodes = parse()
    r1, trace1, calls, checkpoints = structured(nodes, SEED)
    r2, trace2 = flat_path(nodes, SEED)
    assert r1 == r2 == WANTED
    assert trace1 == trace2
    assert [x["node"] for x in checkpoints] == [133, 174, 175, 141]
    summary = {
        "status": "PASS",
        "scope": "Finite first source root only; binary bootstrap/pruning are separate obligations",
        "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        "register_order": ["N", "T", "W", "A", "D", "H", "X", "Y", "L"],
        "initial": SEED, "final": WANTED,
        "structured_edge_calls": calls, "primitive_events": len(trace1),
        "two_literal_interpreters_agree": True,
        "checkpoints": checkpoints,
    }
    (ROOT / "formalism_dirty_seed_result.json").write_text(json.dumps(summary, indent=2) + "\n")
    (ROOT / "formalism_dirty_seed_trace.json").write_text(json.dumps(trace1, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
