#!/usr/bin/env python3
"""Independent finite arithmetic audit of the successful machine's frames.

No imported decoder, path-arithmetic, symbolic-execution, or simulator code is
used. This checks pointer normalization, gap closure, physical/logical register
conversion, state counting/renumbering, and the 54 immediate bootstrap locks.
It does not rerun the macro proofs or claim to be a proof-assistant kernel.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

CANONICAL_SHA256 = "17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13"
OLD_SHA256 = "f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267"
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def table(path):
    transitions, start = {}, None
    for line in path.read_text().splitlines():
        if line.startswith("#! start "):
            start = int(line.split()[-1])
        elif line and not line.startswith("#"):
            a, b, c, d, e = line.split()
            q, bit, write, target = map(int, (a, b, c, e))
            assert bit in (0, 1) and write in (0, 1) and d in ("L", "R")
            assert (q, bit) not in transitions
            transitions[q, bit] = write, d, target
    assert start is not None
    return transitions, start


def increment(word):
    """Integer arithmetic independently checks fixed-width binary increment."""
    width = len(word)
    number = int(word, 2) if width else 0
    carry = number + 1 == 2 ** width
    residue = (number + 1) % (2 ** width)
    return (format(residue, f"0{width}b") if width else ""), carry


def truncate(word, symbol, count):
    """Cut immediately before the count-th occurrence counted from the right."""
    if count == 0:
        return word
    indices = [i for i, bit in enumerate(word) if bit == symbol]
    return word[:indices[-count]] if len(indices) >= count else ""


def verify(machine, grammar, lock):
    machine, grammar, lock = Path(machine), Path(grammar), Path(lock)
    assert digest(machine / "machine.tm") == CANONICAL_SHA256
    assert digest(machine / "machine_old.tm") == OLD_SHA256
    new, start = table(machine / "machine.tm")
    old, old_start = table(machine / "machine_old.tm")
    assert start == 0 and old_start == 95
    assert {q for q, _ in new} == set(range(245))
    assert len(new) == 490 and {t for _, _, t in new.values()} - set(range(245)) == {245}
    mapping = {int(k): v for k, v in json.loads((machine / "renumbering.json").read_text())["old_to_canonical"].items()}
    assert mapping[95] == 0 and mapping[254] == 245
    assert {(mapping[q], b): (w, d, mapping[t]) for (q, b), (w, d, t) in old.items()} == new

    sites = json.loads((machine / "sites_logical.json").read_text())
    physical_sites = json.loads((machine / "sites_physical.json").read_text())
    assert [[p, op, PHYSICAL[r] if op in ("CI", "CD") else r] for p, op, r in sites] == physical_sites
    leaves = {p: (op, r) for p, op, r in sites}
    assert len(leaves) == len(sites) == 6460
    assert all(set(p) <= {"0", "1"} and p for p in leaves)
    assert all(0 <= r < 9 for p, op, r in sites if op in ("CI", "CD"))
    prefixes = {p[:i] for p in leaves for i in range(len(p))}
    assert not prefixes.intersection(leaves)
    assert len(prefixes) == 6459
    assert all(p + b in prefixes or p + b in leaves for p in prefixes for b in "01")
    depth = max(map(len, leaves))
    zero_run = max(len(run) for p in leaves for run in p.split("1"))
    assert depth == 51 and zero_run == 6

    def decode_zero_extension(word):
        p = ""
        for i in range(depth):
            p += word[i] if i < len(word) else "0"
            if p in leaves:
                assert "1" not in word[len(p):], (word, p, "nonzero ignored suffix")
                return p
        raise AssertionError("A complete finite tree did not decode")

    padding = 64
    normalized, overflow_cases, deltas = 0, [], Counter()
    minimum_constant_gap = padding
    case = 0
    for p, op, r in sites:
        for zero in ((True, False) if op == "CD" else (None,)):
            extra = int(op == "CD" and not zero)
            if op == "CI" or (op == "CD" and not zero):
                successor, overflow = increment(p)
            elif op == "CD":
                successor, overflow = increment(truncate(p, "0", 1))
            elif op == "CB":
                successor, overflow = increment(truncate(p, "0", r))
            elif op == "CC":
                successor, overflow = truncate(p, "1", r), False
            else:
                assert op == "CH"
                case += 1
                continue
            delta = extra + int(overflow)
            deltas[delta] += 1
            if overflow:
                overflow_cases.append(case)
            canonical_pointer = decode_zero_extension(successor)
            constant_gap = padding + delta - len(successor)
            minimum_constant_gap = min(minimum_constant_gap, constant_gap)
            assert constant_gap >= 0
            # Appending the SAME n zeroes to both sides proves this word
            # equality for every n >= 0, without testing any chosen bound.
            assert successor + "0" * constant_gap == canonical_pointer + "0" * (padding + delta - len(canonical_pointer))
            normalized += 1
            case += 1
    assert normalized == 8390 and case == 8391
    root_pointer = decode_zero_extension("")
    assert root_pointer + "0" * (padding - len(root_pointer)) == "0" * padding

    boot = json.loads((machine / "blank_boot.json").read_text())
    assert boot["blank_steps"] == 407915
    assert (boot["start"], boot["dispatcher"], boot["head"], boot["marker"], boot["header"]) == (95, 96, -5, -6, 176)
    assert boot["header_distance"] == 181 and boot["pc"] == ""
    assert boot["physical_registers"] == [0, 0, 0, 3, 0, 0, 3, 0, 0]
    assert [boot["physical_registers"][r] for r in PHYSICAL] == [3, 0, 0, 0, 3, 0, 0, 0, 0]
    assert boot["logical_registers"] == [3, 0, 0, 0, 3, 0, 0, 0, 0]
    assert boot["spare_values"] == [1] * 167
    # Parse the ENTIRE represented finite frame; equality also excludes stray
    # one-cells between blocks or beyond the declared tail.
    ones, position = {-6, 176}, 177
    for value in boot["physical_registers"] + boot["spare_values"]:
        position += 1
        ones.update(range(position, position + value + 1))
        position += value + 1
    assert sorted(ones) == boot["all_one_positions"] and len(ones) == boot["one_count"] == 351

    data = json.loads(grammar.read_text())
    rules = {w: (a, b) for w, a, b in data["rules"]}
    assert len(rules) == 128 and all(w == a + b for w, (a, b) in rules.items())
    rows = lock.read_text().splitlines()
    assert int(rows[0]) == len(rows) - 1 == 54
    for line in rows[1:]:
        w, bit, child = line.split()
        assert rules[w][int(bit)] == child
    return {
        "status": "PASS", "canonical_sha256": CANONICAL_SHA256,
        "old_label_sha256": OLD_SHA256, "working_states": 245,
        "canonical_transitions": 490, "canonical_halt_state": 245,
        "renumbering_exact": True, "source_tree_nodes": 6459,
        "source_instruction_sites": 6460, "source_guarded_cases": case,
        "maximum_path_depth": depth, "maximum_zero_run": zero_run,
        "nonhalting_successors_normalized": normalized,
        "full_path_overflow_case_indices": overflow_cases,
        "gap_increment_histogram": dict(deltas),
        "minimum_constant_padding_after_full_successor": minimum_constant_gap,
        "padding": padding, "initial_gap": 181, "initial_affine_parameter": 117,
        "affine_parameter_update": "n' = n + positive_decrement + full_path_carry_overflow",
        "root_zero_extension_leaf": root_pointer,
        "exact_reported_frame_reconstructed": True,
        "spare_count": 167, "spare_values": "all 1",
        "spare_invariant": "K' = K+1 for CI; K'=K for every other nonhalting operation",
        "bootstrap_lock_immediate_projections_checked": 54,
        "dirty_root_specialization": "DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0",
        "logical_tail_convention": "L2.enc sets registers >=9 to zero; physical spare blocks are auxiliary storage",
        "scope": "Independent finite frame/pointer/composition checks. Macro and blank-run execution proofs are separate inputs."
    }


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--machine", type=Path, required=True)
    ap.add_argument("--grammar", type=Path, required=True)
    ap.add_argument("--lock", type=Path, required=True)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    if not __debug__:
        ap.error("Assertions are required; do not use -O.")
    result = verify(args.machine, args.grammar, args.lock)
    output = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
    print(output, end="")
