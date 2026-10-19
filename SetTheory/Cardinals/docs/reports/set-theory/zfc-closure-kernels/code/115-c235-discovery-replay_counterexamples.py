#!/usr/bin/env python3
"""Replay two rejected decoder variants on explicit finite runtime frames.

Python standard library only; the supplied baseline is read as data.  This
script proves no property of the accepted 235-state machine and makes no claim
that either rejected frame occurs on a blank run.  A literal blank-startup
comparison is included as a separate finite observation in the second receipt.

Example:
  python3 discovery/replay_counterexamples.py \
      --baseline-dir /path/to/zfc236-research-20261019 \
      --output-dir /tmp/rejected-counterexamples
"""

import argparse
import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
PHYSICAL_REGISTER_POSITIONS = (6, 2, 0, 4, 3, 7, 8, 5, 1)
BASELINE_FILES = {
    "machines/zfc236_old.tm":
        "ff059535876bc9e1e1e63174ebfd1c10a91c1a818ba0c3f8c4ef2ac51a3cfcc3",
    "source/sites_logical.json":
        "1ebe9691507b2d3236951a31d6b9a7ef548a2cdf90525cd57051992f8ac2626f",
}
CASES = (
    {
        "name": "zero_run7",
        "leaf_index": 648,
        "table_sha256":
            "0748a0a301475c05bbb68a3f4c7511c55a86497caa99077a40f4dba9e783d623",
        "sites_sha256":
            "98d665c973abb5299bcfc849be630a0542d9cab7dc03a29941ef632e381c3ca9",
        "site": ["1110100100110110101010000000", "CI", 1],
        "baseline_site": ["111010010011011010101000000", "CI", 1],
        "first_return_steps": 150,
        "first_clean_return_steps": 666,
        "baseline_steps": 584,
        "reason": "Four decoder reassociations create a seven-zero source run, "
                  "violating the runtime boundary-scanning context.",
    },
    {
        "name": "borrowed_bit105",
        "leaf_index": 195,
        "table_sha256":
            "79a28f4e9016af2d520a4dbeffd39b8f4b1904ed11a48f15f2f2fdbbbc70fa4b",
        "sites_sha256":
            "9d0212868858500f5e26e183b11c60574425a702133378afcf26010892a7ca05",
        "site": ["111010010011001011010", "CI", 7],
        "baseline_site": ["1110100100110010110010", "CI", 7],
        "first_return_steps": 82,
        "first_clean_return_steps": 82,
        "baseline_steps": 618,
        "reason": "The R105/123 repair changes a predecessor bit inspected by "
                  "the backward hardware selector reached through state 81.",
    },
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def read_pinned(path, digest):
    data = path.read_bytes()
    require(sha256(data) == digest, "SHA-256 mismatch: " + str(path))
    return data.decode("utf-8")


def parse_table(text):
    table = {}
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        require(len(parts) == 5, "A transition must have five fields")
        q, b, w, direction, target = parts
        q, b, w, target = map(int, (q, b, w, target))
        require(b in (0, 1) and w in (0, 1), "Nonbinary transition")
        require(direction in ("L", "R"), "Unexpected head move")
        require((q, b) not in table, "Duplicate transition")
        table[q, b] = (w, -1 if direction == "L" else 1, target)
    states = {q for q, _ in table}
    require(len(states) == 236 and len(table) == 472, "Expected 236 complete states")
    require(95 in states and 96 in states and 254 not in states, "Wrong interface states")
    require(all((q, b) in table for q in states for b in (0, 1)), "Incomplete table")
    require(all(target in states or target == 254 for _, _, target in table.values()),
            "Undefined nonhalting target")
    return table


def parse_sites(text):
    sites = json.loads(text)
    require(isinstance(sites, list) and len(sites) == 6455, "Wrong source census")
    require(all(isinstance(s, list) and len(s) == 3
                and isinstance(s[0], str) and set(s[0]) <= {"0", "1"}
                for s in sites), "Malformed source leaf list")
    return sites


def frame(pc, registers, spares, gap=0):
    """Marker at -1, source bits from 0, header at 64+gap, unary files."""
    require(len(pc) < 52, "Fixture exceeds the program-field clearance")
    require(len(registers) == 9 and len(spares) >= 1, "Invalid fixture")
    require(all(isinstance(v, int) and v >= 0 for v in registers + spares),
            "Invalid register value")
    physical = [0] * 9
    for logical_index, physical_index in enumerate(PHYSICAL_REGISTER_POSITIONS):
        physical[physical_index] = registers[logical_index]
    ones = {-1, 64 + gap} | {i for i, bit in enumerate(pc) if bit == "1"}
    position = 65 + gap
    for value in physical + spares:
        position += 1
        ones.update(range(position, position + value + 1))
        position += value + 1
    return ones


def describe(q, head, ones):
    return {"state": q, "head": head, "ones": sorted(ones),
            "all_other_cells": 0}


def expected_increment(site, registers, spares):
    pc, operation, index = site
    require(operation == "CI", "This replay contains only increment controls")
    number = int(pc, 2) + 1
    require(number < 2 ** len(pc), "Unexpected source-counter overflow")
    successor = format(number, "0" + str(len(pc)) + "b")
    updated = list(registers)
    updated[index] += 1
    updated_spares = list(spares) + [1]
    return describe(96, 0, frame(successor, updated, updated_spares)), {
        "pc": successor,
        "logical_registers": updated,
        "spares": updated_spares,
        "gap": 0,
    }


def clean_dispatch(q, head, ones):
    """Recognize a complete unary runtime frame at the dispatcher interface.

    A state-96 visit alone need not be a valid runtime-frame return: both the
    baseline and a rejected control can visit it inside an instruction with an
    incomplete frame.  This detector waits for a well-formed frame.
    """
    if q != 96 or head - 1 not in ones or any(p < head - 1 for p in ones):
        return False
    right = sorted(p for p in ones if p >= head + 52)
    if not right or right[0] < head + 64:
        return False
    position = right[0] + 1
    last = max(ones)
    fields = 0
    while position < last:
        if position in ones or position + 1 not in ones:
            return False
        position += 1
        while position in ones:
            position += 1
        fields += 1
    return position == last + 1 and fields >= 10


def run(table, pc, registers, spares, limit=10000):
    q, head = 96, 0
    ones = frame(pc, registers, spares)
    initial = describe(q, head, ones)
    trace, visits, first_return = [], [], None
    for tick in range(limit):
        bit = int(head in ones)
        require((q, bit) in table, "Unexpected halt before a clean redispatch")
        write, move, target = table[q, bit]
        trace.append([tick, q, head, bit, write, move, target])
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        q, head = target, head + move
        if q != 96:
            continue
        clean = clean_dispatch(q, head, ones)
        visits.append({"steps": tick + 1, "head": head, "clean": clean})
        if first_return is None:
            first_return = {"steps": tick + 1, "clean": clean,
                            "configuration": describe(q, head, ones)}
        if clean:
            return {
                "initial": initial,
                "first_state96_return": first_return,
                "first_clean_redispatch": {
                    "steps": tick + 1, "configuration": describe(q, head, ones)},
                "state96_visits": visits,
                "trace_columns": ["step", "state", "head", "read", "write",
                                  "head_move", "target_state"],
                "trace": trace,
            }
    raise ValueError("No clean redispatch within the explicit finite limit")


def difference(actual, expected):
    actual_ones, expected_ones = set(actual["ones"]), set(expected["ones"])
    return {
        "same_state": actual["state"] == expected["state"],
        "same_head": actual["head"] == expected["head"],
        "missing_one_cells": sorted(expected_ones - actual_ones),
        "extra_one_cells": sorted(actual_ones - expected_ones),
    }


def first_blank_difference(baseline, rejected, limit=409835):
    """Compare actions along a common literal blank-tape prefix."""
    q, head, ones = 95, 0, set()
    for tick in range(limit):
        bit = int(head in ones)
        old_action = baseline[q, bit]
        new_action = rejected[q, bit]
        if old_action != new_action:
            require(tick == 12742, "Unexpected first startup action difference")
            return {
                "status": "REPRODUCED_FINITE_STARTUP_DIFFERENCE",
                "equal_steps_before_different_action": tick,
                "step_numbering": "Zero-based transition index; configurations "
                                  "are still equal immediately before this action.",
                "common_configuration": describe(q, head, ones),
                "read": bit,
                "action_columns": ["write", "head_move", "target_state"],
                "baseline_action": list(old_action),
                "rejected_action": list(new_action),
                "scope": "Finite startup observation, not a claim about eventual halting.",
            }
        write, move, target = old_action
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        q, head = target, head + move
    raise ValueError("The expected finite blank-startup difference was not found")


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-dir", type=Path, required=True,
                        help="Extracted, pinned zfc236-research-20261019 directory")
    parser.add_argument("--output-dir", type=Path,
                        default=HERE.parent / "evidence" / "rejected_counterexamples")
    args = parser.parse_args()
    baseline_text = {name: read_pinned(args.baseline_dir / name, digest)
                     for name, digest in BASELINE_FILES.items()}
    baseline = parse_table(baseline_text["machines/zfc236_old.tm"])
    baseline_sites = parse_sites(baseline_text["source/sites_logical.json"])
    registers, spares = [0] * 9, [0]
    summaries = []
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for case in CASES:
        inputs = HERE / "rejected" / case["name"]
        rejected = parse_table(read_pinned(inputs / "basis236.tm", case["table_sha256"]))
        sites = parse_sites(read_pinned(inputs / "sites_logical.json", case["sites_sha256"]))
        index = case["leaf_index"]
        site, baseline_site = sites[index], baseline_sites[index]
        require(site == case["site"] and baseline_site == case["baseline_site"],
                "Pinned source leaf mismatch")
        require(site[1:] == baseline_site[1:], "Source operations do not correspond")
        expected, logical = expected_increment(site, registers, spares)
        baseline_expected, baseline_logical = expected_increment(baseline_site, registers, spares)
        actual = run(rejected, site[0], registers, spares)
        old_actual = run(baseline, baseline_site[0], registers, spares)
        first = actual["first_state96_return"]
        clean = actual["first_clean_redispatch"]
        old_clean = old_actual["first_clean_redispatch"]
        require(first["steps"] == case["first_return_steps"], "First-return count changed")
        require(clean["steps"] == case["first_clean_return_steps"], "Clean-return count changed")
        require(old_clean["steps"] == case["baseline_steps"], "Baseline step count changed")
        require(clean["configuration"] != expected, "The rejected clean return unexpectedly passed")
        require(old_clean["configuration"] == baseline_expected, "The baseline control did not pass")
        receipt = {
            "status": "PASS_REPRODUCED_FINITE_COUNTEREXAMPLE",
            "name": case["name"],
            "scope": "Explicit valid runtime-frame counterexample for this rejected "
                     "236-state basis; no claim that this frame is blank-run reachable "
                     "and no proof claim about the accepted 235-state machine.",
            "reason_for_rejection": case["reason"],
            "input_sha256": {
                "baseline": BASELINE_FILES,
                "rejected/basis236.tm": case["table_sha256"],
                "rejected/sites_logical.json": case["sites_sha256"],
            },
            "source_leaf_index_zero_based": index,
            "site": site,
            "baseline_site": baseline_site,
            "logical_registers": registers,
            "spares": spares,
            "gap": 0,
            "header_distance": 64,
            "expected_configuration": expected,
            "expected_logical_result": logical,
            "rejected_execution": actual,
            "state96_visit_note": "State 96 can occur inside an instruction with an "
                                  "incomplete frame, including on the baseline. "
                                  "The first state-96 visit is diagnostic only; "
                                  "the counterexample compares the first clean redispatch.",
            "first_return_difference": difference(first["configuration"], expected),
            "first_clean_redispatch_difference": difference(clean["configuration"], expected),
            "baseline_same_source_leaf_passed": True,
            "baseline_expected_configuration": baseline_expected,
            "baseline_expected_logical_result": baseline_logical,
            "baseline_execution": old_actual,
            "checker_sha256": sha256(Path(__file__).read_bytes()),
        }
        if case["name"] == "borrowed_bit105":
            receipt["blank_startup_first_action_difference"] = first_blank_difference(baseline, rejected)
        filename = case["name"] + ".json"
        write_json(args.output_dir / filename, receipt)
        summaries.append({
            "name": case["name"], "status": receipt["status"], "receipt": filename,
            "receipt_sha256": sha256((args.output_dir / filename).read_bytes()),
            "first_state96_return_steps": first["steps"],
            "first_return_is_clean": first["clean"],
            "first_clean_redispatch_steps": clean["steps"],
            "baseline_same_leaf_steps": old_clean["steps"],
        })
    summary = {"status": "PASS_TWO_REJECTED_CONTROLS_REPRODUCED",
               "scope": "Finite rejected-runtime controls only.", "controls": summaries}
    write_json(args.output_dir / "summary.json", summary)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
