#!/usr/bin/env python3
"""Portable literal witnesses for the naive 245 -> 244 scanner contraction.

Inputs are the reconstructed source 68 package.  No repository import, solver,
or third-party Python package is needed.  This verifies exact finite traces and
the claimed site census; the accompanying note gives the symbolic local lemma.
It does not infer anything about this candidate's ultimate blank-tape outcome.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path


def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        q, bit, write, direction, target = line.split()
        key = int(q), int(bit)
        assert key not in table
        assert direction in ("L", "R")
        table[key] = int(write), -1 if direction == "L" else 1, int(target)
    states = {q for q, _ in table}
    assert set(table) == {(q, bit) for q in states for bit in (0, 1)}
    return table


def encode_table(table):
    lines = ["#! start 95"]
    for (q, bit), (write, direction, target) in sorted(table.items()):
        lines.append(f"{q} {bit} {write} {'R' if direction == 1 else 'L'} {target}")
    return "\n".join(lines) + "\n"


def step(table, state, head, ones):
    write, direction, target = table[state, int(head in ones)]
    if write:
        ones.add(head)
    else:
        ones.discard(head)
    return target, head + direction


def paint(pc, header_distance, registers, spares):
    assert header_distance >= len(pc) + 2
    assert len(registers) == 9 and spares
    ones = {-1, header_distance}
    ones.update(i for i, bit in enumerate(pc) if bit == "1")
    pos = header_distance + 1
    for value in registers + spares:
        assert value >= 0
        ones.update(range(pos + 1, pos + value + 2))
        pos += value + 2
    return ones


def find_marked_scan(table, pc, initial, fuel=10000):
    """Run a genuine instruction frame to the scanner's appended phase zero."""
    state, head, ones = 96, 0, set(initial)
    for ticks in range(fuel):
        if state == 4 and head == len(pc) and head not in ones and head + 1 in ones:
            assert {-1} | {i for i, bit in enumerate(pc) if bit == "1"} == {
                i for i in ones if i < len(pc)
            }
            return ticks, ones
        state, head = step(table, state, head, ones)
    raise AssertionError("Did not reach the marked-phase scanner window")


def scanner_trace(table, head, initial, fuel=1000):
    state, ones = 4, set(initial)
    trace = []
    for ticks in range(fuel):
        trace.append(dict(step=ticks, state=state, head=head, read=int(head in ones)))
        if state == 96:
            assert ones == initial, "Scanner unexpectedly changed the tape"
            return trace
        state, head = step(table, state, head, ones)
    raise AssertionError("Scanner did not redispatch")


def max_zero_run(word):
    return max(map(len, word.split("1")))


def trailing_zero_run(word):
    return len(word) - len(word.rstrip("0"))


def check_full_prefix_code(words):
    trie = {}
    for word in words:
        branch = trie
        for bit in word:
            assert "leaf" not in branch
            branch = branch.setdefault(bit, {})
        assert not branch, "Duplicate word or prefix collision"
        branch["leaf"] = True

    def visit(node):
        if "leaf" in node:
            assert set(node) == {"leaf"}
            return
        assert set(node) == {"0", "1"}, "Incomplete binary tree"
        visit(node["0"])
        visit(node["1"])

    visit(trie)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", required=True, type=Path,
                        help="Root of the reconstructed zfc245-proof-20261018 package")
    parser.add_argument("--output", type=Path, default=Path("scanner-witness.json"))
    parser.add_argument("--candidate-output", type=Path,
                        help="Optionally write the exact rejected 244-state table")
    parser.add_argument("--affine-result", type=Path,
                        help="Optionally compare with second_scan_result.json")
    args = parser.parse_args()
    table_path = args.package / "machine/zfc245_old.tm"
    sites_path = args.package / "certificate/sites_physical.json"
    baseline = read_table(table_path)
    assert len(baseline) == 490
    expected_chain = [4, 6, 9, 13, 19, 29, 41, 58]
    for i, state in enumerate(expected_chain):
        assert baseline[state, 0] == (0, -1, expected_chain[i + 1] if i + 1 < 8 else 84)
        assert baseline[state, 1] == (1, -1, 4)
    assert baseline[84, 0] == (0, 1, 84)
    assert baseline[84, 1] == (1, 1, 96)
    candidate = dict(baseline)
    candidate[41, 0] = 0, -1, 84
    del candidate[58, 0]
    del candidate[58, 1]
    assert len(candidate) == 488
    assert all(target != 58 for _, _, target in candidate.values())

    sites = json.loads(sites_path.read_text())
    assert len(sites) == 6460
    check_full_prefix_code([pc for pc, _, _ in sites])
    long_tail = {i for i, (pc, _, _) in enumerate(sites) if trailing_zero_run(pc) >= 6}
    any_long_run = {i for i, (pc, _, _) in enumerate(sites) if max_zero_run(pc) >= 6}
    assert long_tail == any_long_run
    assert len(long_tail) == 50
    kind_counts = Counter(sites[i][1] for i in long_tail)
    assert kind_counts == {"CD": 49, "CI": 1}
    assert all(trailing_zero_run(pc) == 0 for pc, op, _ in sites if op not in ("CI", "CD"))
    assert max(max_zero_run(pc) for pc, _, _ in sites) == 6

    witnesses = []
    for site_index, positive in ((41, False), (41, True), (649, False)):
        pc, kind, register = sites[site_index]
        assert trailing_zero_run(pc) == 6 and "1" in pc
        registers = [0] * 9
        registers[register] = int(positive)
        initial = paint(pc, 64, registers, [1])
        base_ticks, base_window = find_marked_scan(baseline, pc, initial)
        short_ticks, short_window = find_marked_scan(candidate, pc, initial)
        assert base_window == short_window
        base_trace = scanner_trace(baseline, len(pc), base_window)
        short_trace = scanner_trace(candidate, len(pc), short_window)
        assert base_trace[-1]["head"] == 0
        assert [line["state"] for line in short_trace] == [4, 6, 9, 13, 19, 29, 41, 84, 96]
        assert [line["head"] for line in short_trace] == [len(pc) - i for i in range(8)] + [len(pc) - 6]
        assert [line["read"] for line in short_trace] == [0] * 7 + [1, 0]
        assert short_trace[-1]["head"] != 0
        witnesses.append(dict(
            site_index=site_index, pc=pc, operation=kind, physical_register=register,
            decrement_guard=("positive" if positive else "zero") if kind == "CD" else None,
            initial_frame=dict(state=96, head=0, header_distance=64,
                               physical_registers=registers, spares=[1],
                               one_cells=sorted(initial)),
            baseline_steps_to_local_window=base_ticks,
            candidate_steps_to_local_window=short_ticks,
            local_one_cells=sorted(base_window),
            baseline_scanner_trace=base_trace,
            candidate_scanner_trace=short_trace,
        ))

    guarded_indices = {(i, zero) for i in long_tail
                       for zero in ((True, False) if sites[i][1] == "CD" else (None,))}
    assert len(guarded_indices) == 99
    affine_comparison = None
    if args.affine_result:
        result = json.loads(args.affine_result.read_text())
        observed = {(item["index"], item["zero"]) for item in result["failures"]}
        assert observed == guarded_indices
        assert result["passed"] == 8292
        affine_comparison = dict(passed=8292, failed=99, exact_predicted_failure_set=True)

    encoded = encode_table(candidate)
    out = dict(
        status="PASS",
        scope="Exact finite witnesses plus site census; no blank-tape outcome claim",
        baseline_sha256=hashlib.sha256(table_path.read_bytes()).hexdigest(),
        sites_sha256=hashlib.sha256(sites_path.read_bytes()).hexdigest(),
        candidate_sha256=hashlib.sha256(encoded.encode()).hexdigest(),
        mutation=dict(delete_state=58, patch="41 0 0 L 84", working_states=244),
        scanner_thresholds=dict(baseline=8, candidate=7),
        site_census=dict(total=6460, complete_binary_prefix_tree=True,
                         maximum_zero_run=6, maximum_trailing_zero_run=6,
                         tail_at_least_6=len(long_tail), kinds=dict(kind_counts),
                         indices=sorted(long_tail), guarded_cases=99,
                         all_other_operation_kinds_end_in_1=True,
                         any_run_at_least_6_equals_tail_at_least_6=True),
        witnesses=witnesses,
        inherited_affine_result_comparison=affine_comparison,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n")
    if args.candidate_output:
        args.candidate_output.parent.mkdir(parents=True, exist_ok=True)
        args.candidate_output.write_text(encoded)
    print(json.dumps(dict(status="PASS", concrete_witnesses=len(witnesses),
                          guarded_failure_census=len(guarded_indices),
                          candidate_sha256=out["candidate_sha256"])))


if __name__ == "__main__":
    main()
