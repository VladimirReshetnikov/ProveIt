#!/usr/bin/env python3
"""Check the finite inductive certificate for PA194HA -> PA194HAZ.

This program imports no compiler, interpreter, or symbolic simulator.  Its
inputs are the two *resolved* nine-register source instruction arrays.  A
decrement is ["dec", register, zero_target, positive_target]; a successful
positive test decreases that register by one, while the zero test leaves it
unchanged.  Instructions use natural-number registers.

Proof justified by the checks below:
  I(pc,r) := (pc in {3550,3551,3552,3553} implies r[6] == 0).
  I holds initially at pc=25 (indeed at every pc outside this set).
  Every external edge into this set is a zero branch of a decrement of r[6].
  Every internal step preserves r[6]=0, so I is inductive for either source.
  The only changed instruction is at 3553.  There I forces the new decrement
  to take its zero branch, performing exactly the old jump with no register
  change.  Induction on the number of steps gives identical source
  configurations at every time, for arbitrary initial natural registers.

The certificate proves source equivalence.  Blank-tape initialization and
the compiler-to-Turing-machine refinement are separate obligations.
"""

import argparse
import hashlib
import json
from pathlib import Path


SITE_COUNT = 3650
ENTRY = 25
ZERO_REGISTER = 6
CUT = frozenset((3550, 3551, 3552, 3553))
BOUNDARY = frozenset(((3545, 3551), (3548, 3550)))
OLD_CUT = {
    3550: ["jump", 3553],
    3551: ["dec", 1, 3553, 3552],
    3552: ["jump", 3551],
    3553: ["jump", 3637],
}
NEW_LAST = ["dec", 6, 3637, 3554]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def targets(instruction):
    op = instruction[0]
    if op == "jump":
        return instruction[1:]
    if op in ("inc", "dec"):
        return instruction[2:]
    return []


def validate(program):
    require(type(program) is list, "The program must be a JSON array")
    require(len(program) == SITE_COUNT, "Expected exactly 3650 source sites")
    arities = {"halt": 1, "jump": 2, "inc": 3, "dec": 4}
    for pc, instruction in enumerate(program):
        require(type(instruction) is list and len(instruction) > 0,
                f"Malformed instruction at {pc}")
        op = instruction[0]
        require(type(op) is str and op in arities,
                f"Unknown operation at {pc}")
        require(len(instruction) == arities[op], f"Wrong arity at {pc}")
        if op in ("inc", "dec"):
            register = instruction[1]
            require(type(register) is int and 0 <= register < 9,
                    f"Invalid register at {pc}")
        for destination in targets(instruction):
            require(type(destination) is int and 0 <= destination < len(program),
                    f"Invalid destination at {pc}")


def check_invariant(program):
    validate(program)
    require(ENTRY not in CUT, "The invariant must hold initially")
    boundary = set()
    for pc, instruction in enumerate(program):
        if pc in CUT:
            # No register instruction inside the cut can increase r[6].
            require(instruction[:2] != ["inc", ZERO_REGISTER],
                    f"An internal edge can destroy the invariant at {pc}")
        else:
            for destination in targets(instruction):
                if destination in CUT:
                    require(instruction[0] == "dec"
                            and instruction[1] == ZERO_REGISTER
                            and instruction[2] == destination
                            and instruction[3] != destination,
                            f"An incoming edge lacks a zero guard: {pc}->{destination}")
                    boundary.add((pc, destination))
    require(boundary == BOUNDARY, f"Unexpected cut boundary: {sorted(boundary)}")
    return sorted(boundary)


def verify(before, after):
    validate(before)
    validate(after)
    differences = [pc for pc, pair in enumerate(zip(before, after)) if pair[0] != pair[1]]
    require(differences == [3553], f"Unexpected instruction differences: {differences}")
    for pc, instruction in OLD_CUT.items():
        require(before[pc] == instruction, f"Unexpected old cut instruction at {pc}")
    require(after[3553] == NEW_LAST, "Unexpected replacement instruction")
    old_boundary = check_invariant(before)
    new_boundary = check_invariant(after)
    require(old_boundary == new_boundary, "The boundary changed")
    return {
        "result": "PASS",
        "sites": SITE_COUNT,
        "entry": ENTRY,
        "changed_site": 3553,
        "before": before[3553],
        "after": after[3553],
        "invariant_sites": sorted(CUT),
        "zero_register": ZERO_REGISTER,
        "boundary_zero_edges": old_boundary,
        "scope": "identical configurations at every source step from pc=25, for all initial natural registers",
        "method": "exhaustive finite control-graph check of an inductive invariant; no bounded simulation",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before", type=Path, help="HA resolved instruction JSON")
    parser.add_argument("after", type=Path, help="HAZ resolved instruction JSON")
    args = parser.parse_args()
    old_bytes = args.before.read_bytes()
    new_bytes = args.after.read_bytes()
    receipt = verify(json.loads(old_bytes), json.loads(new_bytes))
    receipt["before_file_sha256"] = hashlib.sha256(old_bytes).hexdigest()
    receipt["after_file_sha256"] = hashlib.sha256(new_bytes).hexdigest()
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
