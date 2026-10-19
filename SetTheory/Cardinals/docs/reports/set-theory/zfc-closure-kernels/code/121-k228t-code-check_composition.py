#!/usr/bin/env python3
"""Check the finite source/frame glue in the K230 -> K228 proof.

This standard-library-only checker reads data, imports no other project code,
and does not simulate a bounded sample of register values.  It independently
checks the exact source replacement, lexical control scope, and the finite
successor-to-leaf zero-padding identities needed to iterate the universal
runtime certificate.  The natural-number induction for the transfer macro,
and the soundness of the runtime certificate rules, are mathematical lemmas
given in composition.tex, not claims of this data audit.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path


def require(condition, explanation):
    if not condition:
        raise ValueError(explanation)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def atom(op, operand=None):
    return ("L", op, operand)


def pair(left, right):
    return ("N", left, right)


U = pair(pair(atom("CD", 6), pair(atom("CI", 5), atom("CC", 2))), atom("CI", 5))
V = pair(atom("CI", 5), pair(atom("CD", 6), atom("CC", 2)))


def source(path):
    rows = json.loads(Path(path).read_text())
    leaves = {}
    prefixes = set()
    for row in rows:
        require(isinstance(row, list) and len(row) == 3, "Malformed source row")
        word, op, operand = row
        require(isinstance(word, str) and 0 < len(word) < 64
                and set(word) <= {"0", "1"}, "Malformed source path")
        require(word not in leaves, "Duplicate source path")
        require(op in {"CI", "CD", "CB", "CC", "CH"}, "Unknown opcode")
        if op == "CH":
            require(operand is None, "Halt operand")
        else:
            require(type(operand) is int, "Nonintegral operand")
            require(0 <= operand < 9 if op in {"CI", "CD"} else operand > 0,
                    "Register range or nonpositive control depth")
        leaves[word] = atom(op, operand)
        prefixes.update(word[:i] for i in range(len(word)))
    require(not set(leaves) & prefixes, "A leaf is an internal prefix")
    require(len(prefixes) == len(leaves) - 1, "Incorrect full tree size")
    require(all(p + b in leaves or p + b in prefixes for p in prefixes for b in "01"),
            "Source is not a complete binary tree")

    def descend(prefix):
        if prefix in leaves:
            return leaves[prefix]
        return pair(descend(prefix + "0"), descend(prefix + "1"))

    return rows, leaves, prefixes, descend("")


def signature(tree):
    """Break depth, continue depth, and possible halt; natural truncated pred."""
    if tree[0] == "L":
        _, op, operand = tree
        return (1 if op == "CD" else operand if op == "CB" else 0,
                operand if op == "CC" else 0, op == "CH")
    b0, c0, h0 = signature(tree[1])
    b1, c1, h1 = signature(tree[2])
    return max(max(b0 - 1, 0), b1), max(c0, max(c1 - 1, 0)), h0 or h1


def replace_macros(tree, path="", occurrences=None):
    if occurrences is None:
        occurrences = []
    if tree == U:
        occurrences.append(path)
        return V
    if tree[0] == "L":
        return tree
    return pair(replace_macros(tree[1], path + "0", occurrences),
                replace_macros(tree[2], path + "1", occurrences))


def increment(word):
    """Fixed-width binary increment, independently using a reversed carry loop."""
    digits = list(word)
    carry = 1
    for j in range(len(digits) - 1, -1, -1):
        if carry:
            if digits[j] == "0":
                digits[j], carry = "1", 0
            else:
                digits[j] = "0"
    return "".join(digits), carry


def strip(word, bit, count):
    j = len(word)
    while j and count:
        j -= 1
        if word[j] == bit:
            count -= 1
    return word[:j]


def successor(word, op, operand, positive):
    if op in {"CI", "CD"} and (op == "CI" or positive):
        return increment(word)
    if op in {"CD", "CB"}:
        return increment(strip(word, "0", 1 if op == "CD" else operand))
    if op == "CC":
        return strip(word, "1", operand), 0
    raise ValueError("Halt has no successor")


def next_leaf(word, leaves, prefixes):
    prefix = ""
    while prefix not in leaves:
        require(prefix in prefixes, "Walk reached missing node")
        prefix += word[len(prefix)] if len(prefix) < len(word) else "0"
    # This is equality of the actual infinite-zero padded instruction words.
    require(word.rstrip("0") == prefix.rstrip("0"), "Stray nonzero instruction bit")
    require(word + "0" * (64 - len(word)) == prefix + "0" * (64 - len(prefix)),
            "Base-frame word identity failed")
    return prefix


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--package", type=Path, default=Path(__file__).resolve().parents[1],
                    help="Archive root; defaults to the parent of the code directory")
    for name in ("release-sites", "old-source", "new-source", "runtime", "boot", "output"):
        ap.add_argument("--" + name, type=Path)
    args = ap.parse_args()
    defaults = {"release_sites": "inputs/sites230.json", "old_source": "inputs/sites230_logical.json",
                "new_source": "machines/sites228.json", "runtime": "evidence/runtime_k228.json",
                "boot": "evidence/startup_k228.json", "output": "evidence/composition.json"}
    for name, relative in defaults.items():
        if getattr(args, name) is None:
            setattr(args, name, args.package / relative)
    old_rows, old_leaves, old_prefixes, old_tree = source(args.old_source)
    new_rows, leaves, prefixes, new_tree = source(args.new_source)
    require(sha(args.release_sites) ==
            "400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487",
            "Unpinned K230 release site listing")
    opcodes = {"EInc": "CI", "EDecnz": "CD", "EBreak": "CB", "EContinue": "CC", "EHalt": "CH"}
    converted = []
    for word, edge in json.loads(args.release_sites.read_text()):
        fields = edge.split()
        converted.append([word, opcodes[fields[0]], None if len(fields) == 1 else int(fields[1])])
    require(converted == old_rows, "Old logical source differs from pinned release")
    occurrences = []
    require(replace_macros(old_tree, occurrences=occurrences) == new_tree,
            "Source differs beyond the stated macro replacement")
    require(len(occurrences) == 4 and len(old_rows) == 5125 and len(new_rows) == 5121,
            "Incorrect occurrence or leaf counts")
    require(signature(U) == signature(V) == (0, 0, False), "Macro has escaping control")
    require(signature(old_tree) == signature(new_tree) == (0, 0, True), "Program root scope")
    require(max(map(len, leaves)) == 40, "Unexpected source depth")

    runtime = json.loads(args.runtime.read_text())
    boot = json.loads(args.boot.read_text())
    require(runtime["status"] == "UNIVERSAL_MATHEMATICAL_PASS", "Incomplete runtime")
    require(boot["status"] == "PASS_EXACT_BLANK_STARTUP_TWO_ENGINES", "Incomplete startup")
    require(runtime["table_sha256"] == boot["table_sha256"] ==
            "2b791ed22523b9610d43d7440631b27063089d2d1a24cf3bfbe5ace6cf416ea2",
            "Table identity mismatch")
    require(runtime["source_sha256"] == sha(args.new_source), "Runtime source mismatch")
    cases_path = args.runtime.parent / runtime["cases_file"]
    require(sha(cases_path) == runtime["cases_sha256"], "Case receipt hash mismatch")
    cases = json.loads(cases_path.read_text())
    expected = {(i, p) for i, (_, op, _) in enumerate(new_rows)
                for p in ((False, True) if op == "CD" else (False,))}
    require(len(cases) == len(expected) == 6656, "Wrong runtime case count")
    require({(c["site_index"], c["positive"]) for c in cases} == expected, "Missing case")
    require(runtime["rows"] == len(runtime["used_rows"]) == 456 and runtime["unused_rows"] == [],
            "Row coverage receipt mismatch")

    kinds, examples = collections.Counter(), {}
    nonhalting, overflowing = 0, 0
    minimum_duration = min(c["duration"][0] for c in cases)
    require(minimum_duration == 13, "Unexpected positive progress bound")
    for c in cases:
        require(len(c["duration"]) == 13 and all(type(x) is int and x >= 0 for x in c["duration"]),
                "Duration is not coefficientwise nonnegative")
        word, op, operand = new_rows[c["site_index"]]
        if op == "CH":
            continue
        succ, overflow = successor(word, op, operand, c["positive"])
        target_leaf = next_leaf(succ, leaves, prefixes)
        require(c["motion"] == [-overflow] + [0] * 12, "Counter-overflow head motion")
        delta = int(op == "CD" and c["positive"])
        require(64 + delta + overflow >= max(len(succ), len(target_leaf)), "Insufficient next frame")
        kind = ("same_leaf" if succ == target_leaf else
                "extend_with_zeroes" if len(succ) < len(target_leaf) else "discard_trailing_zeroes")
        kinds[kind] += 1
        examples.setdefault(kind, {"source": word, "op": op, "positive": c["positive"],
                                   "successor": succ, "next_leaf": target_leaf})
        nonhalting += 1
        overflowing += overflow

    entry_leaf = next_leaf("", leaves, prefixes)
    require(entry_leaf == "000", "Changed zero-padded entry leaf")
    require(boot["literal_steps"] == 409835 and boot["endpoint_state"] == 84
            and boot["endpoint_head"] == -5, "Unexpected blank entry")
    # Check the entire support encoded in the boot receipt against the frame.
    physical_seed = [0, 0, 0, 3, 0, 0, 3, 0, 0]
    values = physical_seed + [1] * 167
    support, position = {-6, 176}, 177
    for value in values:
        support.update(range(position + 1, position + value + 2))
        position += value + 2
    require(boot["complete_support"] == sorted(support), "Boot does not have the exact seeded frame")
    require(len(support) == 351, "Unexpected boot support cardinality")

    result = {
        "status": "PASS_SOURCE_AND_FRAME_COMPOSITION",
        "checker_sha256": sha(__file__),
        "release_sites_sha256": sha(args.release_sites),
        "old_source_sha256": sha(args.old_source), "new_source_sha256": sha(args.new_source),
        "runtime_receipt_sha256": sha(args.runtime), "boot_receipt_sha256": sha(args.boot),
        "source_replacement": {"occurrences": occurrences, "old_leaves": len(old_rows),
                               "new_leaves": len(new_rows), "macro_signature": signature(U),
                               "root_signature": signature(new_tree)},
        "all_leaf_guard_cases": len(expected), "halting_cases": len(expected) - nonhalting,
        "nonhalting_successor_identities": nonhalting, "overflow_cases": overflowing,
        "successor_kinds": dict(kinds), "successor_examples": examples,
        "maximum_source_depth": 40, "minimum_total_instruction_area": 64,
        "frame_growth": "G' = G + positive_decrement + counter_overflow; head' = head - counter_overflow",
        "minimum_actual_steps": minimum_duration,
        "entry_leaf": entry_leaf, "blank_startup_steps": 409835,
        "initial_total_instruction_area": 181, "initial_extra_gap": 117,
        "physical_seed": physical_seed, "initial_spares": {"length": 167, "constant": 1},
        "scope": "Finite exact source and frame-composition audit. Mathematical induction and upstream logical calibration are separately stated; no new Rocq kernel check is claimed.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ["status", "all_leaf_guard_cases", "halting_cases",
                      "nonhalting_successor_identities", "overflow_cases", "successor_kinds",
                      "minimum_actual_steps", "entry_leaf"]}, indent=2))


if __name__ == "__main__":
    main()
