#!/usr/bin/env python3
"""PA194TDY universal literal-tape verification.
Uses the unmodified, separately represented unary-list checker in vendor/.
It rederives all four list-sweep lemmas from the actual candidate rows.
It assumes no arithmetic-box oracle. This is executable mathematical evidence,
not an end-to-end proof-assistant proof or a PA proof-code compiler.
"""
from pathlib import Path
import hashlib, importlib.util, json, sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1]
VENDOR = HERE / "vendor"
OUT = HERE / "recorded"
if not __debug__ or sys.flags.optimize:
    raise RuntimeError("Run without -O or PYTHONOPTIMIZE")
spec = importlib.util.spec_from_file_location("literal_vendor_check", VENDOR / "check.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
sym, runtime, source = checker.sym, checker.runtime, checker.source
sym.HEADER_BASE = 48

def sha(b):
    return hashlib.sha256(b).hexdigest()

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    native = BASE / "artifacts/pa194_tdy.native.tm"
    dense_path = BASE / "artifacts/pa194_tdy.tm"
    assert sha(native.read_bytes()) == "2f6e2342151be7c9f7fb8025f81063525c5d276605d2fa87535a9c7d1498755d"
    assert sha(dense_path.read_bytes()) == "84bfe1368312c7c71c9e4706de7cb65923310e25f8d472997c9c57c5aedd7934"
    rows, states, halt = checker.parse(native, 194)
    dense, dense_states, dense_halt = checker.parse(dense_path, 194)
    assert halt == 254 and dense_halt == 194 and dense_states == set(range(194))
    labels = json.loads((BASE / "artifacts/pa194_tdy.labels.json").read_text())
    assert len(labels) == 195 and len(set(labels)) == 195 and labels[0] == 74 and labels[-1] == 254
    assert {(labels[q], b): (w, d, labels[t]) for (q, b), (w, d, t) in dense.items()} == rows

    physical = (6, 3, 0, 4, 5, 7, 8, 2, 1)
    sites = json.loads((BASE / "source/sites.json").read_text())
    opcode = {"inc": "CI", "dec": "CD", "breakTo": "CB", "continueTo": "CC", "halt": "CH"}
    mapped = [[p, opcode[op], arg] for p, op, arg in sites]
    graph, _ = source.graph_arithmetic(mapped)
    assert graph == source.graph_intervals(mapped)
    names = {"identity": "jump", "increment": "inc", "decrement": "dec", "halt": "halt"}
    instructions = [[names[e[0]]] + e[1:] + targets for e, targets in graph]
    assert instructions == json.loads((BASE / "source/instructions.json").read_text())
    assert instructions == json.loads((VENDOR / "reference_inputs/195S.instructions.json").read_text())
    assert len(sites) == 3673 and max(len(p) for p, op, arg in sites) <= 48

    mapping = {int(k): v for k, v in json.loads((VENDOR / "reference/legacy_mapping.json").read_text()).items()}
    for q in states | {halt}:
        mapping.setdefault(q, q + 10000)
    assert len({mapping[q] for q in states | {halt}}) == 195
    assert mapping[84] == 96 and mapping[254] == 254
    table = {(mapping[q], b): (w, 1 if d == "R" else -1, mapping[t])
             for (q, b), (w, d, t) in rows.items()}
    runtime.PHY = physical
    lemmas, blocks = sym.prove_blocks(table)
    assert len(blocks) == 4
    print("Four generic unary-list sweep lemmas rederived from the candidate rows.", flush=True)

    contracts = []
    total = 0
    maximum = 0
    for i, site in enumerate(mapped):
        for positive in ([False, True] if site[1] == "CD" else [False]):
            result = sym.case(table, lemmas, site, positive)
            total += result["symbolic_steps"]
            maximum = max(maximum, result["symbolic_steps"])
            contracts.append({"site": i, "positive": positive, "duration": result["duration"],
                              "motion": result["motion"], "symbolic_steps": result["symbolic_steps"]})
        if (i + 1) % 1000 == 0:
            print("PA194TDY checked sites", i + 1, flush=True)
    assert len(contracts) == 4780
    assert all(sym.nonnegative(x["duration"]) and x["duration"][0] > 0 for x in contracts)

    # Independent complete-tape bytearray startup.
    tape = bytearray(20000)
    origin = 10000
    head = origin
    q = 74
    for step in range(57594):
        assert q != 254 and 0 <= head < len(tape)
        w, d, q = rows[q, tape[head]]
        tape[head] = w
        head += 1 if d == "R" else -1
    assert q == 84 and head - origin == -2
    pc = sites[25][0]
    frame = bytearray([1] + [int(b) for b in pc] + [0] * (48 - len(pc)) + [1])
    logical = [2] + [0] * 8
    values = [None] * 9
    for i, j in enumerate(physical):
        values[j] = logical[i]
    for value in values + [1] * 26:
        frame.extend([0] + [1] * (value + 1))
    expected = bytearray(len(tape))
    first = head - 1
    expected[first:first + len(frame)] = frame
    assert tape == expected

    encoded = (json.dumps(contracts, separators=(",", ":")) + "\n").encode()
    (OUT / "contracts.json").write_bytes(encoded)
    (OUT / "list_lemmas.json").write_text(json.dumps(blocks, indent=2) + "\n")
    seed = {"state": q, "head": head - origin, "ones": [i - origin for i, b in enumerate(tape) if b],
            "source_site": 25, "source_path": pc, "header_distance": 48,
            "logical_registers": logical, "physical_registers": values, "spare_values": [1] * 26}
    (OUT / "blank_seed.json").write_text(json.dumps(seed, indent=2) + "\n")
    receipt = {
        "family": "PA194TDY", "status": "PASS", "working_states": 194, "transition_rows": 388,
        "native_sha256": sha(native.read_bytes()), "dense_sha256": sha(dense_path.read_bytes()),
        "dense_native_conjugacy_exact": True, "physical_register_map": physical,
        "source_sites": len(sites), "source_contracts": len(contracts),
        "independent_cfg_resolvers_agree": True, "logical_source_cfg_equal_to_frozen_195S_reference": True,
        "symbolic_steps": total, "maximum_symbolic_steps": maximum,
        "minimum_positive_duration_constant": min(x["duration"][0] for x in contracts),
        "list_lemmas_rederived_from_literal_table": 4, "arithmetic_box_oracles": False,
        "register_scope": "nine independent arbitrary natural values; both decrement outcomes",
        "spare_scope": "arbitrary finite nonempty list of arbitrary natural values",
        "header_scope": "distance 48+n for arbitrary natural n",
        "startup_steps": 57594, "whole_blank_tape_equal": True,
        "contracts_sha256": sha(encoded), "kernel_checked": False,
        "scope": "universal literal source-frame simulation, positive physical durations, dense conjugacy, exact blank startup; corpus novelty and PA logical calibration are separate"
    }
    (OUT / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2), flush=True)

if __name__ == "__main__":
    main()
