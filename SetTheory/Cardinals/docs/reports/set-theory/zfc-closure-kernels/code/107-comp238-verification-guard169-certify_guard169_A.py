#!/usr/bin/env python3
"""Certify old169/read1 right-neighbor guard for the accepted Boundary239 machine.
Adapted from the attributed coordinated239 proof driver by changing only input
hashes and the expected number of rows from480 to478. The identical structural
source validator is repeated with the Boundary239 pin; its original remains
unchanged in the engine. All semantic checks remain.

The neighboring symbolic_runtime.py and independent_runtime.py modules are
the unchanged, attributed incoming80 mathematical checker. This driver
instruments its literal steps without weakening any of its endpoint checks.
Every natural parameter remains symbolic, and the four list inductions are
rederived from the exact old table. A separate exact blank prefix is finite.
This is an executable ordinary mathematical proof, not a Lean/Rocq artifact.

Usage (from any working directory):
  python certify_guard169.py --table zfc_rotation240_old.tm \
      --sites sites_logical.json --output-dir results
"""

from collections import Counter
from pathlib import Path
import argparse
import hashlib
import json
import sys
import time

import symbolic_runtime as s


OLD_SHA = "d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719"
SITES_SHA = "7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6"
CHECKER_SHA = "9ff1b7c487036744206976aa45c16c3b8d6eeb8d4e7cad81f41dae8ebab66c5e"
HELPER_SHA = "0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346"
BOOT_STEPS = 409691


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


# Same structural validator as the unchanged engine; only source pin changes.
def validate_A_inputs(table,sites):
    working={q for q,b in table}
    assert 95 in working and 96 in working and 254 not in working
    assert len(table)==2*len(working) and all((q,b) in table for q in working for b in (0,1))
    assert {row[2] for row in table.values()}-working=={254}
    assert isinstance(sites,list) and len(sites)==6455
    leaves=set();prefixes=set()
    for row in sites:
        assert isinstance(row,list) and len(row)==3
        pc,op,arg=row
        assert isinstance(pc,str) and 0<len(pc)<=64 and set(pc)<={'0','1'}
        assert pc not in leaves
        assert op in ('CI','CD','CB','CC','CH')
        if op=='CH':assert arg is None
        elif op in ('CI','CD'):assert type(arg) is int and 0<=arg<9
        else:assert type(arg) is int and arg>=1
        leaves.add(pc);prefixes.update(pc[:i] for i in range(len(pc)))
    assert not leaves.intersection(prefixes)
    assert all(p+b in leaves or p+b in prefixes for p in prefixes for b in ('0','1'))
    assert len(prefixes)==len(leaves)-1
    # The complete Boundary239 source list is independently source-calibrated separately.
    # Pin its canonical serialization here; generic runtime rules are unchanged.
    encoded=(json.dumps(sites,indent=2)+'\n').encode()
    assert hashlib.sha256(encoded).hexdigest()=='77eda491bdb9c74611bc4bb4d89d86aed4e30a47e2b68fe7a8f4c05821ec58c4'
    return {'working_states':len(working),'leaf_count':len(leaves),'complete_binary_tree':True,'maximum_depth':max(map(len,leaves)),'exact_rotated_source_pin':True,'source_equivalence_checked_separately':True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--table", type=Path, required=True)
    parser.add_argument("--sites", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    assert __debug__ and not sys.flags.optimize, "Run without -O or PYTHONOPTIMIZE."
    assert digest(args.table) == OLD_SHA, "The old table bytes are not the pinned boundary239 table."
    assert digest(args.sites) == SITES_SHA, "The source site bytes are not the pinned boundary239 source."
    assert digest(Path(s.__file__)) == CHECKER_SHA, "The neighboring symbolic checker changed."
    assert digest(Path(s.r.__file__)) == HELPER_SHA, "The neighboring helper changed."
    table = s.r.table(args.table)
    sites = json.loads(args.sites.read_text())
    input_facts = validate_A_inputs(table, sites)
    lemmas, blocks = s.prove_blocks(table)

    # A visit to state169 cannot be hidden by either kind of induction.
    # The one-block traces expose all interior states, including unary scans.
    assert all(
        169 not in [event[1][0] for event in block["trace"]
                    if event[0] in ("literal", "unary")]
        for block in blocks
    )
    assert all(q != 169 for q, direction, family, reverse in lemmas)
    assert all(table[169, bit][2] != 169 for bit in (0, 1))

    original_step = s.State.step
    visits = []
    site_index = None
    positive_guard = None

    def inspected_step(state, current_table, current_lemmas, clock, motion):
        state.key()  # Normalize runs and check all affine coefficients are nonnegative.
        if state.q == 169:
            assert state.direction == 1, ("Unexpected orientation at state169", site_index, positive_guard)
            atom = state.right[0]
            assert atom[0] == "run" and atom[2][0] >= 1
            if atom[1] == 1:
                # The head scans the first cell of this run. A constant
                # term >=2 guarantees that the right-hand neighbor is1,
                # for every independent assignment of natural parameters.
                assert atom[2][0] >= 2, (
                    "The state169/read1 right-neighbor guard is unproved",
                    site_index, positive_guard, state.key()
                )
                visits.append({
                    "site_index": site_index,
                    "site": sites[site_index],
                    "positive": positive_guard,
                    "run_length": atom[2],
                    "clock": clock,
                    "head_motion": motion,
                })
        return original_step(state, current_table, current_lemmas, clock, motion)

    started = time.monotonic()
    records = []
    used = set()
    s.State.step = inspected_step
    try:
        for index, site in enumerate(sites):
            for positive in ((False, True) if site[1] == "CD" else (False,)):
                site_index = index
                positive_guard = positive
                before = len(visits)
                answer = s.case(table, lemmas, site, positive)
                used.update(answer["rows"])
                records.append({
                    "site_index": index,
                    "positive": positive,
                    "symbolic_steps": answer["symbolic_steps"],
                    "duration": answer["duration"],
                    "motion": answer["motion"],
                    "guard_visits": len(visits) - before,
                })
                if len(records) % 1000 == 0:
                    print("PASS", len(records), "instruction guards; right-neighbor visits",
                          len(visits), "seconds", round(time.monotonic() - started, 2), flush=True)
    finally:
        s.State.step = original_step

    assert len(records) == 8386 and len(used) == 478
    assert visits, "The guard proof must include nonvacuous state169/read1 cases."

    # This additional calculation proves only the prescribed finite old
    # blank initialization. Runtime continuation is covered symbolically.
    state = 95
    head = 0
    ones = set()
    boot_visits = Counter()
    for step in range(BOOT_STEPS):
        bit = int(head in ones)
        if state == 169 and bit == 1:
            assert head + 1 in ones, ("Blank-prefix guard failure", step, head)
            boot_visits["169/1_nextone"] += 1
        write, direction, target = table[state, bit]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        state = target
        head += direction
    assert (state, head, len(ones)) == (96, -5, 351)

    summary = {
        "status": "PASS_UNIVERSAL_RUNTIME_AND_EXACT_BOOT_GUARD",
        "table_sha256": OLD_SHA,
        "source_sha256": SITES_SHA,
        "checker_sha256": CHECKER_SHA,
        "helper_sha256": HELPER_SHA,
        "instrument_sha256": digest(Path(__file__)),
        "input_validation": input_facts,
        "cases": len(records),
        "symbolic_rules": sum(case["symbolic_steps"] for case in records),
        "minimum_actual_instruction_steps": min(case["duration"][0] for case in records),
        "next_one_guard_visits": len(visits),
        "minimum_certified_one_run_length_constant": min(visit["run_length"][0] for visit in visits),
        "all_runtime_rows": len(used),
        "bootstrap_steps": BOOT_STEPS,
        "bootstrap_guard_visits": dict(boot_visits),
        "no_summarized_169_visits": True,
        "blocks": blocks,
        "seconds": time.monotonic() - started,
        "guard": (
            "Whenever old state169 reads1, the immediately right-hand cell is1. "
            "Universal over valid instruction frames and the exact blank prefix."
        ),
        "scope": (
            "Finite affine/list proof with arbitrary natural primary register values, "
            "additional gap, first spare value, and arbitrary finite remaining spare list. "
            "Whole-tape endpoint checks and positive clocks are inherited unchanged. "
            "This is an ordinary mathematical proof, not a Lean/Rocq kernel proof."
        ),
        "loop_bound_scope": (
            "The underlying 4000-rule cap bounds proof construction only. It does not "
            "bound actual steps, natural register values, gap, or finite spare-list length."
        ),
        "execution": {
            "python_version": sys.version,
            "optimization": sys.flags.optimize,
            "argv": sys.argv,
        },
    }
    args.output_dir.mkdir(parents=True, exist_ok=True)
    write_json(args.output_dir / "guard169_universal.json", summary)
    write_json(args.output_dir / "guard169_visits.json", visits)
    write_json(args.output_dir / "guard169_cases.json", records)
    print(json.dumps({key: value for key, value in summary.items() if key != "blocks"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
