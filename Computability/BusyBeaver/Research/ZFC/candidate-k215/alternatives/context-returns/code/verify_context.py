#!/usr/bin/env python3
"""Independent finite proof checker for the five context-dependent retargetings.

Only the Python standard library is needed. This checker does not import the
allocator, the source decoder, or the symbolic runtime. It verifies the finite
premises of the stuttering proof in the report, then replays the entire blank
prefix on both the native and dense presentations. It does not decide Con(ZFC).
"""
from collections import deque
from pathlib import Path
import argparse
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parent.parent
BASE_SHA = "9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2"
NEW_SHA = "da20914ad9bda3f75de0381f2c05a7b5e67d26199b57b870a5ea3b72511ab627"
CHANGES = {
    (13, 1): (1, -1, 81),
    (27, 1): (0, -1, 302),
    (83, 1): (0, -1, 57),
    (156, 1): (1, 1, 52),
    (198, 0): (1, -1, 54),
}
CLAIMS = [
    (13, 1, {-2: 1, -1: 0, 0: 1}, 2, 4),
    (13, 1, {-1: 1, 0: 1}, 3, 3),
    (27, 1, {-1: 0, 0: 1}, 2, 2),
    (83, 1, {-1: 1, 0: 1}, 2, 2),
    (156, 1, {0: 1, 1: 1}, 2, 2),
    (198, 0, {-1: 1, 0: 0}, 2, 2),
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_table(path):
    rows, starts = {}, []
    for line in path.read_text().splitlines():
        if line.startswith("#! start "):
            starts.append(int(line.split()[-1]))
        elif line and not line.startswith("#"):
            q, r, w, direction, target = line.split()
            q, r, w, target = map(int, (q, r, w, target))
            require(direction in ("L", "R") and r in (0, 1) and w in (0, 1), "bad row")
            require((q, r) not in rows, "duplicate row")
            rows[q, r] = w, (1 if direction == "R" else -1), target
    states = {q for q, _ in rows}
    require(starts == [0], "start must be zero")
    require(set(rows) == {(q, r) for q in states for r in (0, 1)}, "partial table")
    terminals = {z for _, _, z in rows.values()} - states
    require(len(terminals) == 1, "exactly one separate terminal required")
    return rows, next(iter(terminals))


def canonical(table, halt):
    """Unique rooted read-labelled breadth-first numbering, halt last."""
    labels = {0: 0}
    todo = [0]
    for q in todo:
        for r in (0, 1):
            z = table[q, r][2]
            if z != halt and z not in labels:
                labels[z] = len(labels)
                todo.append(z)
    require(set(labels) == {q for q, _ in table}, "graph-unreachable working state")
    labels[halt] = len(labels)
    dense = {(labels[q], r): (w, d, labels[z]) for (q, r), (w, d, z) in table.items()}
    return dense, labels


def serialize(table):
    return ("#! start 0\n" + "".join(
        f"{q} {r} {w} {'R' if d == 1 else 'L'} {z}\n"
        for (q, r), (w, d, z) in sorted(table.items())
    )).encode("ascii")


def incoming(table, target):
    return [(q, r, w, d) for (q, r), (w, d, z) in table.items() if z == target]


def two_step_histories(table, target):
    """Overapproximation: keep the most recent write at every visited cell.

    Some enumerated paths can be infeasible because an earlier read conflicts
    with a write. Retaining those paths only makes the guard test stronger.
    Positions are relative to the final head; every actual two-step suffix is
    included, and its final tape agrees with all recorded latest writes.
    """
    result = []
    for middle, read1, write1, move1 in incoming(table, target):
        middle_head = -move1
        for origin, read0, write0, move0 in incoming(table, middle):
            origin_head = middle_head - move0
            known = {origin_head: write0}
            known[middle_head] = write1
            result.append({"origin": origin, "middle": middle, "known": known})
    return result


def local_run(table, state, context, length):
    tape, head, trace = dict(context), 0, []
    for index in range(length):
        require(head in tape, "local proof read an unspecified exterior cell")
        r = tape[head]
        w, d, z = table[state, r]
        if index:
            require((state, r) not in CHANGES, "modified row in strict macro interior")
        trace.append([state, head, r, w, d, z])
        tape[head], head, state = w, head + d, z
    return (state, head, tape), trace


def expected_frame():
    # Physical register order: W,L,T,D,A,Y,N,H,X, with logical N=4.
    values = [0, 0, 0, 0, 0, 0, 4, 0, 0] + [1] * 40
    ones, cursor = {-9, 57}, 58
    for value in values:
        cursor += 1  # initial zero of the unary token
        ones.update(range(cursor, cursor + value + 1))
        cursor += value + 1
    require(len(ones) == 95 and max(ones) == 199, "bad frame reconstruction")
    return ones


def blank_run(table, steps):
    q, head, ones = 0, 0, set()
    delay_hits = 0
    for _ in range(steps):
        r = int(head in ones)
        if (q, r) == (13, 1) and head - 1 not in ones:
            delay_hits += 1
        w, d, z = table[q, r]
        if w:
            ones.add(head)
        else:
            ones.discard(head)
        q, head = z, head + d
    return q, head, ones, delay_hits


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "evidence/context-check.json")
    args = parser.parse_args()
    base_path, new_path = ROOT / "upstream/k215.native.tm", ROOT / "machine/k215-context.native.tm"
    require(hashlib.sha256(base_path.read_bytes()).hexdigest() == BASE_SHA, "baseline hash")
    require(hashlib.sha256(new_path.read_bytes()).hexdigest() == NEW_SHA, "candidate hash")
    old, old_halt = read_table(base_path)
    new, new_halt = read_table(new_path)
    require(old_halt == new_halt == 254, "native halt convention")
    require(set(old) == set(new) and len(new) == 430, "working-state count")
    require({k: new[k] for k in new if new[k] != old[k]} == CHANGES, "exact five-row delta")
    histories = []
    for name, table in (("baseline", old), ("candidate", new)):
        hist = two_step_histories(table, 13)
        require(bool(hist), "missing histories")
        for entry in hist:
            known = entry["known"]
            if known.get(0, 1) == 1:
                require(known.get(-1) == 1 or (known.get(-1) == 0 and known.get(-2) == 1), "q13 guard")
        first_step = {table[0, r][2] for r in (0, 1)}
        require(13 != 0 and 13 not in first_step, "q13 too early for history lemma")
        histories.append({"table": name, "histories": hist})
        for q, _, context, _, _ in CLAIMS[2:]:
            neighbor = next(x for x in context if x != 0)
            ins = incoming(table, q)
            require(bool(ins) and q != 0, "no incoming guard")
            require(all(d == -neighbor and w == context[neighbor] for _, _, w, d in ins), "immediate predecessor guard")
    blocks = []
    for q, r, context, nold, nnew in CLAIMS:
        endpoint0, trace0 = local_run(old, q, context, nold)
        endpoint1, trace1 = local_run(new, q, context, nnew)
        require(endpoint0 == endpoint1, "different final whole tapes")
        require(nold > 0 and nnew > 0, "nonpositive block duration")
        blocks.append({"entry": [q, r], "context": context, "baseline_trace": trace0, "candidate_trace": trace1,
                       "endpoint": endpoint0, "arbitrary_unvisited_exterior": True})
    d0, labels0 = canonical(old, 254)
    d1, labels1 = canonical(new, 254)
    require(len(labels1) == 216, "215 working states plus halt")
    differences = [[*k, list(d0[k]), list(d1[k])] for k in sorted(d0) if d0[k] != d1[k]]
    require(bool(differences), "mere rooted state relabelling")
    dense_bytes = serialize(d1)
    (ROOT / "machine/k215-context.tm").write_bytes(dense_bytes)
    (ROOT / "machine/native-to-dense.json").write_text(json.dumps(labels1, indent=2, sort_keys=True) + "\n")
    frame = expected_frame()
    q0, h0, tape0, hits0 = blank_run(old, 95714)
    q1, h1, tape1, hits1 = blank_run(new, 95740)
    qd, hd, taped, _ = blank_run(d1, 95740)
    require((q0, h0, tape0) == (84, -8, frame), "baseline startup")
    require((q1, h1, tape1) == (84, -8, frame), "candidate startup")
    require((qd, hd, taped) == (labels1[84], -8, frame), "dense startup")
    require(hits0 == hits1 == 13 and 95740 - 95714 == 2 * hits1, "startup clock change")
    st = json.loads(gzip.decompress((ROOT / "evidence/startup.json.gz").read_bytes()))
    require((st["state"], st["head"], st["steps"], set(st["one_cells"])) == (84, -8, 95740, frame), "runtime startup binding")
    runtime = json.loads((ROOT / "evidence/runtime.json").read_text())
    require(runtime["table_sha256"] == NEW_SHA and runtime["proved_cases"] == runtime["expected_cases"] == 6176 and not runtime["failures"], "runtime receipt binding")
    result = {"status": "PASS", "baseline_sha256": BASE_SHA, "candidate_sha256": NEW_SHA,
              "dense_sha256": hashlib.sha256(dense_bytes).hexdigest(), "working_states": 215, "transitions": 430,
              "all_states_graph_reachable": True, "rooted_labelled_graphs_nonisomorphic": True,
              "first_canonical_difference": differences[0], "local_blocks": blocks, "incoming_history_audits": histories,
              "blank_steps": 95740, "baseline_blank_steps": 95714, "extra_delay_hits": 13,
              "blank_frame": {"native_state": 84, "dense_state": labels1[84], "head": -8, "header": 57,
                              "gap": 1, "logical_registers": [4, 0, 0, 0, 0, 0, 0, 0, 0], "spares": [1] * 40,
                              "one_cells": sorted(frame)},
              "scope": "Exact finite premises of the ordinary stuttering proof and full finite blank prefix; not a proof-assistant kernel certificate."}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ("local_blocks", "incoming_history_audits", "blank_frame")}, indent=2))


if __name__ == "__main__":
    main()
