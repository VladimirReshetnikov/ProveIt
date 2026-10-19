#!/usr/bin/env python3
"""Replay a parametric wrong-successor family using the inherited checker.

This refutes the intended next complete frame for the unmodified 245-state
grammar combined with the five-zero scanner. It does not refute an unrelated
consistency equivalence for the experimental machine.
"""
from pathlib import Path
import argparse
import importlib
import json
import sys

sys.dont_write_bytecode = True

INPUT_PC = "11101001001000000"
EXPECTED_PC = "1110100100100001"
WRONG_PC = "11101001001001"


def run(reference, table_path):
    sys.path.insert(0, str(reference / "code"))
    f = importlib.import_module("full_symbolic_parametric")
    f.m.TABLE = f.rebuild.read_table(reference / "certificate/machine_old.tm")[0]
    f.m.prove_blocks()
    f.m.prove_word_identity()
    assert f.paths.full_inc(f.paths.full_strip(INPUT_PC, "0", 1)) == (EXPECTED_PC, False)
    baseline = f.case(INPUT_PC, "CD", 1, True, [[0, 0]] * 9)
    assert baseline["cost"] == "574+8*gap"
    f.m.TABLE = f.rebuild.read_table(table_path)[0]
    f.m.prove_blocks()
    # The word identity is independent of the transition table. Its already
    # checked finite-list induction remains valid after the table change.
    values = [f.E()] * 9

    def frame(pc):
        return f.Conf(96, "R", [f.m.bit(1), f.Blank()],
                      [f.m.bit(int(b)) for b in pc] +
                      [f.Run(0, f.E.var("gap") + (64 - len(pc))), f.m.bit(1)] +
                      f.make_file(values))

    def known_right_bit(conf, offset):
        """Read an offset only when affine lower bounds determine its bit."""
        assert conf.side == "R"
        for atom in conf.right:
            assert isinstance(atom, f.Run)
            if offset < atom.length.c:
                return atom.bit
            assert not atom.length.terms, "Offset is inside an unknown length"
            offset -= atom.length.c
        raise AssertionError("Offset is outside represented runs")

    current, target = frame(INPUT_PC), frame(WRONG_PC)
    f.normalize(current)
    f.normalize(target)
    left_marker = repr(target.left)
    cost, motion, trace, dispatches = f.E(), f.E(), [], []
    for tick in range(3000):
        if trace and current.state == 96:
            is_target = current.key() == target.key()
            if is_target:
                exclusion = None
            elif repr(current.left) != left_marker:
                # All normal dispatch frames have exactly the isolated marker
                # to their left. This comparison includes the entire exterior.
                assert current.side == "R"
                assert isinstance(current.left[0], f.Run) and current.left[0].bit == 1
                assert current.left[0].length.c >= 2 or any(
                    isinstance(atom, f.Run) and atom.bit == 1 and atom.length.c >= 1
                    for atom in current.left[1:])
                exclusion = "Nonblank cells left of the required isolated marker"
            else:
                # Every source path has length <=51 and every frame has D>=64.
                # Therefore a one at relative cell 51 excludes a normal frame.
                assert known_right_bit(current, 51) == 1
                exclusion = "Relative cell 51 is one inside the mandatory zero gap"
            dispatches.append(dict(rule=tick, steps=str(cost), motion=str(motion),
                                   complete_normal_frame=is_target,
                                   exclusion=exclusion, side=current.side,
                                   left=str(current.left), right=str(current.right)))
            if is_target:
                break
        cost, motion = f.step(current, cost, motion, trace)
    else:
        raise AssertionError("Symbolic target was not reached")
    assert str(cost) == "650+8*gap" and motion == f.E()
    assert len(trace) == 245
    assert len(dispatches) == 5
    assert sum(x["complete_normal_frame"] for x in dispatches) == 1
    return dict(
        status="PROVED_WRONG_NEXT_COMPLETE_FRAME_FAMILY",
        experimental_machine_status="UNVALIDATED_244_STATE_EXPERIMENT",
        input_pc=INPUT_PC, instruction="CD", logical_register=1, guard="zero",
        expected_successor=EXPECTED_PC, actual_successor=WRONG_PC,
        physical_registers=[0] * 9,
        header_distance="64+gap; gap is an arbitrary natural number",
        spares="An arbitrary nonempty finite list of natural values",
        baseline_steps=baseline["cost"], experimental_steps=str(cost),
        head_displacement=str(motion), symbolic_rules=len(trace),
        universal_gap_and_spares=True,
        first_complete_frame_checked=True, source_path_length_bound=51,
        claim_limit="Refutes the intended next-frame instruction contract; no conclusion about an unrelated Con(ZFC) equivalence or blank reachability of this input",
        dispatches=dispatches, trace=trace)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--reference", required=True, type=Path)
    ap.add_argument("--table", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    result = run(args.reference.resolve(), args.table.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ("trace", "dispatches")}, indent=2))


if __name__ == "__main__":
    main()
