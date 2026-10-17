#!/usr/bin/env python3
"""Independent literal-table audit of the published 254- and 253-state baselines.

Reads machine data only, imports no upstream code, and performs no downloads.
The finite boot checks are diagnostic finite computations, not substitutes
for the upstream end-to-end Coq proofs or an internal ZFC proof translation.
"""
from __future__ import annotations

import argparse
from collections import deque
import hashlib
import json
from pathlib import Path


BASELINES = {
    254: dict(
        sha256="d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb",
        steps=264982, dispatch=96, gap=62, pc="", head=-8,
        physical=[0, 0, 0, 0, 0, 0, 2, 0, 0], spares=[0] * 136,
        commit="297ab8df7e5de329605c3875b4934643b371a5e3"),
    253: dict(
        sha256="84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95",
        steps=312975, dispatch=33, gap=40, pc="000", head=-17,
        physical=[0, 2, 0, 0, 0, 0, 5, 0, 0],
        spares=[0, 0, 1, 0, 0, 0, 0, 0, 1] + [0] * 149,
        commit="0d544f2a2e3c18f12278441a74b7879f31cbe856"),
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read_table(path, count):
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    require(digest == BASELINES[count]["sha256"], f"{count}: pinned SHA256 mismatch")
    rows, start = {}, None
    for line in data.decode("ascii").splitlines():
        if line.startswith("#! start "):
            require(start is None, "duplicate start declaration")
            start = int(line.split()[-1])
        elif line and not line.startswith("#"):
            q, b, w, direction, target = line.split()
            q, b, w, target = map(int, (q, b, w, target))
            require((q, b) not in rows, "duplicate transition")
            require(b in (0, 1) and w in (0, 1) and direction in ("L", "R"),
                    "invalid binary transition")
            require(0 <= target <= count, "out-of-range transition target")
            rows[q, b] = w, -1 if direction == "L" else 1, target
    require(start == 0, "the literal start must be zero")
    require(set(rows) == {(q, b) for q in range(count) for b in (0, 1)},
            "table must contain exactly two rows per working state")
    return rows, start, digest


def graph_reachable(rows, start, halt):
    seen, todo = {start}, deque([start])
    while todo:
        q = todo.popleft()
        if q == halt:
            continue
        for b in (0, 1):
            target = rows[q, b][2]
            if target not in seen:
                seen.add(target)
                todo.append(target)
    return seen


def exact_step_partition(rows, count):
    # Greatest all-tape state congruence preserving writes, moves, and halting.
    partition = {q: int(q == count) for q in range(count + 1)}
    counts = []
    while True:
        ids, updated = {}, {}
        for q in range(count + 1):
            signature = ("HALT",) if q == count else tuple(
                (w, d, partition[target])
                for w, d, target in (rows[q, 0], rows[q, 1]))
            if signature not in ids:
                ids[signature] = len(ids)
            updated[q] = ids[signature]
        counts.append(len(set(updated[q] for q in range(count))))
        old_equivalence = {(q, r) for q in range(count + 1)
                           for r in range(q + 1, count + 1)
                           if partition[q] == partition[r]}
        new_equivalence = {(q, r) for q in range(count + 1)
                           for r in range(q + 1, count + 1)
                           if updated[q] == updated[r]}
        if old_equivalence == new_equivalence:
            return counts, updated
        partition = updated


def expected_support(spec, head):
    support = {head - 1, head + spec["gap"]}
    for i, b in enumerate(spec["pc"]):
        if b == "1":
            support.add(head + i)
    pos = head + spec["gap"] + 1
    for value in spec["physical"] + spec["spares"]:
        pos += 1  # separator zero
        support.update(range(pos, pos + value + 1))
        pos += value + 1
    return support


def boot(rows, start, spec):
    q, head, ones = start, 0, set()
    for t in range(spec["steps"]):
        require((q, int(head in ones)) in rows, f"unexpected halt at time {t}")
        write, direction, q = rows[q, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction
    require(q == spec["dispatch"], "wrong final dispatch state")
    require("head" not in spec or head == spec["head"], "wrong absolute head")
    require(ones == expected_support(spec, head), "wrong complete infinite-tape support")
    return dict(steps=spec["steps"], state=q, head=head,
                support=sorted(ones), nonzero_cells=len(ones),
                spare_blocks=len(spec["spares"]), entire_tape_verified=True)


def audit(path, count):
    rows, start, digest = read_table(path, count)
    reachable = graph_reachable(rows, start, count)
    require(reachable == set(range(count + 1)), "not every counted state is graph reachable")
    counts, partition = exact_step_partition(rows, count)
    require(len(set(partition.values())) == count + 1, "unexpected nontrivial exact-step quotient")
    return dict(working_states=count, separate_halt=count, symbols=2,
                transitions=len(rows), blank=0, start=start, tape="bi-infinite",
                moves=["L", "R"], sha256=digest, source_commit=BASELINES[count]["commit"],
                graph_reachable_working=count, exact_step_classes=count,
                refinement_working_class_counts=counts,
                boot=boot(rows, start, BASELINES[count]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--machine254", required=True, type=Path)
    parser.add_argument("--machine253", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    report = dict(status="PASS", kernel_rebuilt=False, internal_ZFC_proof_supplied=False,
                  scope="Exact pinned table identities, graph and exact-step quotient checks, "
                        "and finite literal blank-tape bootstrap endpoints only.",
                  baselines=[audit(args.machine254, 254), audit(args.machine253, 253)])
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    for result in report["baselines"]:
        print(f"PASS {result['working_states']} working states; {result['transitions']} rows; "
              f"boot {result['boot']['steps']} literal steps; "
              f"{result['boot']['nonzero_cells']} one-cells; full tape and head checked")
    print("No local kernel rebuild or new internalization claim.")


if __name__ == "__main__":
    main()
