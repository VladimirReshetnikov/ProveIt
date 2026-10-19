#!/usr/bin/env python3
"""Exact raw-Wade pricing and independent finite register-path controls.

This is an experiment, not a binary simulation theorem or a sub-246 result.
The published DAG and pinned compiler are imported as data / code respectively.
Repository sources are not modified.  EReturn exists only in a test wrapper.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
from math import isqrt
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parent / "ProveIt"
INPUTS = HERE / "inputs"
RECOVERY = (INPUTS / "recover_wade_dag.py" if INPUTS.is_dir() else
            REPO / "Computability/BusyBeaver/Research/ZFC/recover_wade_dag.py")
spec = importlib.util.spec_from_file_location("recover_wade_dag", RECOVERY)
recovery = importlib.util.module_from_spec(spec)
spec.loader.exec_module(recovery)
sys.path.insert(0, str(HERE / "wade_copy"))
import TMBuilder as backend
from tm import Transition

# Each immutable source dictionary is retained in this cache, so its object
# identifier cannot be recycled.  Only pure walk results are memoized.
WRAPPERS = {}


def patched(nodes, names):
    nodes, names = dict(nodes), dict(names)
    assert len(nodes) == 219
    assert nodes[152] == ("EInc 6", "ENode 153")
    assert nodes[153] == ("ENode 132", "ENode 170")
    assert nodes[132] == ("ENode 123", "EHalt")
    nodes.update({
        219: ("EDecnz 5", "EBreak 1"),
        220: ("ENode 219", "EHalt"),
        221: ("EDecnz 5", "EContinue 4"),
        222: ("EDecnz 5", "ENode 221"),
        223: ("ENode 220", "ENode 222"),
        224: ("EDecnz 5", "ENode 223"),
    })
    for q in range(219, 225):
        names[q] = f"atomicTest.{q - 219}"
    nodes[152] = ("ENode 224", "ENode 170")
    return nodes, names


def compile_evidence(tag, nodes, names):
    machine = recovery.compile_dag(backend, nodes, names)
    states = {q for q, _ in machine.states}
    live_nodes = {q: pair for q, pair in nodes.items() if names[q] in states}
    live_names = {q: names[q] for q in live_nodes}
    recovery.reextract(machine, live_nodes, live_names)
    missing = [(q, bit) for q in sorted(states) for bit in ("0", "1")
               if (q, bit) not in machine.states]
    assert missing == [("1.inc", "1")], missing
    machine.states["1.inc", "1"] = Transition("1", "R", "halt")
    framework = {q for q in states if q[0].isdigit()}
    out = HERE / f"{tag}-raw-wade.tm"
    machine.save(str(out))
    return {
        "working_states": len(states),
        "decision_states": len(states - framework),
        "framework_states": len(framework),
        "totalized_transition_rows": len(machine.states),
        "totalization": {"state": "1.inc", "read": 1,
                         "write": 1, "move": "R", "target": "halt"},
        "dead_DAG_nodes": [q for q in nodes if q not in live_nodes],
        "reextracted_live_DAG_exact": True,
        "terminal_targets": sorted({a.nextstate for a in machine.states.values()} - states),
        "start": machine.start,
        "table_sha256": hashlib.sha256(out.read_bytes()).hexdigest(),
    }


def inc_path(path):
    out = list(path)
    for i in range(len(out) - 1, -1, -1):
        out[i] = 1 - out[i]
        if out[i]:
            break
    return tuple(out)


def strip_path(bit, k, path):
    i = len(path)
    while k and i:
        i -= 1
        if path[i] == bit:
            k -= 1
    return path[:i]


def break_path(k, path):
    return inc_path(strip_path(0, k, path))


def continue_path(k, path):
    return strip_path(1, k, path)


def walk(nodes, root, path):
    q, i = root, 0
    for _ in range(len(nodes) + 1):
        bit = path[i] if i < len(path) else 0
        edge = nodes[q][bit]
        i += 1
        if edge.startswith("ENode "):
            q = int(edge.split()[1])
        else:
            return edge, (path + (0,) * i)[:i]
    raise AssertionError("decoder fuel exhausted")


def run_wrapper(nodes, entry, values, max_steps=100000, trace=False):
    # A binary parent, exactly as for a compiled sequence, separates return
    # from a genuine halt. This wrapper is never compiled as a machine.
    key = id(nodes), entry
    if key not in WRAPPERS:
        wrapped = dict(nodes)
        root = max(nodes) + 1
        wrapped[root] = (f"ENode {entry}", "EReturn")
        WRAPPERS[key] = (nodes, wrapped, root, {})
    _, nodes, root, decoded = WRAPPERS[key]
    path, values, steps, log = (), list(values), 0, []
    while steps < max_steps:
        if path not in decoded:
            decoded[path] = walk(nodes, root, path)
        edge, consumed = decoded[path]
        if trace:
            log.append((steps, edge, list(consumed), list(values)))
        if edge in ("EHalt", "EReturn"):
            return edge, values, steps, log
        kind, param = edge.split()
        param = int(param)
        if kind == "EInc":
            values[param] += 1
            path = inc_path(consumed)
        elif kind == "EDecnz":
            if values[param]:
                values[param] -= 1
                path = inc_path(consumed)
            else:
                path = break_path(1, consumed)
        elif kind == "EBreak":
            path = break_path(param, consumed)
        elif kind == "EContinue":
            path = continue_path(param, consumed)
        else:
            raise AssertionError(edge)
        steps += 1
    raise AssertionError(("test step bound exhausted", entry, values, path))


def unpair(n):
    k = (isqrt(8 * n + 1) - 1) // 2
    b = n - k * (k + 1) // 2
    return k - b, b


def verify_macro(nodes):
    cases = 0
    traces = {}
    cycle_cost = None
    residue_costs = {}
    for h in range(1024):
        initial = [13, 17, 19, 23, 29, h, 31, 37, 41]
        event, out, steps, log = run_wrapper(nodes, 224, initial, trace=h < 9)
        expected_event = "EHalt" if h % 4 == 1 else "EReturn"
        assert event == expected_event, (h, event)
        expected = initial.copy()
        expected[5] = 0
        assert out == expected, (h, out, expected)
        if h < 4:
            residue_costs[h] = steps
        if h == 4:
            cycle_cost = steps - residue_costs[0]
        if h >= 4:
            assert steps == cycle_cost * (h // 4) + residue_costs[h % 4]
        if h < 9:
            traces[h] = log
        cases += 1
    return {"tested_H_interval": [0, 1023], "cases": cases,
            "all_outputs_exact": True, "cycle_cost": cycle_cost,
            "terminal_costs_by_H_mod_4": residue_costs,
            "clock_unit": "executed nonterminal RegisterPath leaves; terminal leaf excluded",
            "small_exact_traces": traces}


def verify_full_nip(old, new):
    cases = 0
    maximum_steps = {"old": 0, "atomic": 0}
    preserved_others = [0, 1, 3, 4, 8]
    for h in range(128):
        for w in range(64):
            # Changing sentinels avoid a zero-valued-field equality check
            # accidentally concealing corruption. Scratch is genuinely zero.
            initial = [2 + h % 5, 17 + w % 7, w, 23, 29, h, 0, 0, 41]
            for label, nodes in (("old", old), ("atomic", new)):
                event, out, steps, _ = run_wrapper(nodes, 152, initial)
                should_halt = h == 1 if label == "old" else h % 4 == 1
                assert (event == "EHalt") == should_halt, (label, h, w, event)
                if not should_halt:
                    expected = initial.copy()
                    expected[5], expected[2] = unpair(w)
                    assert event == "EReturn" and out == expected, (label, h, w, out, expected)
                else:
                    assert all(out[r] == initial[r] for r in preserved_others)
                maximum_steps[label] = max(maximum_steps[label], steps)
                cases += 1
    return {"H_interval": [0, 127], "W_interval": [0, 63],
            "cases": cases, "all_full_outputs_exact": True,
            "maximum_executed_nonterminal_leaves": maximum_steps,
            "scratch_entry_assumption": "X=Y=0",
            "nonhalting_endpoint": "same N,T,A,D,L; (H,W)=unP(W_in); X=Y=0"}


def main():
    source_path = "ZF/m254/coq/prog/Dag254.v"
    source = ((INPUTS / "Dag254.v").read_bytes() if INPUTS.is_dir() else
              recovery.git_bytes(None, source_path))
    assert hashlib.sha256(source).hexdigest() == recovery.SOURCE_SHA256[source_path]
    nodes, names = recovery.parse_dag(source.decode())
    new_nodes, new_names = patched(nodes, names)
    pricing = {"original": compile_evidence("original", nodes, names),
               "atomic_target": compile_evidence("atomic-target", new_nodes, new_names)}
    macro = verify_macro(new_nodes)
    nip = verify_full_nip(nodes, new_nodes)
    delta = {key: pricing["atomic_target"][key] - pricing["original"][key]
             for key in ("working_states", "decision_states", "framework_states",
                         "totalized_transition_rows")}
    evidence = {
        "source_commit": "79957d7b290ec807d434959a0c6ecc06ee90b419",
        "upstream_commit": recovery.COMMIT,
        "upstream_DAG_sha256": hashlib.sha256(source).hexdigest(),
        "pricing": pricing, "atomic_minus_original": delta,
        "macro": macro, "full_nip": nip,
        "limitations": ["finite interpreter tests are controls, not universal proofs",
                        "no closed Lean theorem for the new source is claimed",
                        "raw Wade pricing is not optimized 246-backend pricing",
                        "no exact-machine simulation theorem for the new table is claimed"],
    }
    (HERE / "atomic-target-evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    printable = dict(evidence)
    printable["macro"] = {key: value for key, value in macro.items() if key != "small_exact_traces"}
    print(json.dumps(printable, indent=2))


if __name__ == "__main__":
    main()
