"""Measure naive 2-adic helper replacement in the recovered unary backend.

The mixed variants deliberately isolate costs and have incompatible encoders
and decoders. Even the matched variant has NO proof-search calibration or Lean
simulation theorem. The point is to measure compiler cost, not to claim that
shorter integer descriptions yield a smaller consistency machine.

The backend comes from the unchanged pinned vendored snapshot by default.
--upstream-clone selects a separate clone at that commit. It is copied and
executed only in an outside-repository scratch directory. No source file in
the snapshot is modified, and no generated machine is installed there.
"""
from __future__ import annotations

import argparse
import importlib
import json
from pathlib import Path
import sys

from recover_wade_dag import (COMMIT, ROOT, REGISTERS, builder_from_dag,
                             git_bytes, parse_dag)


def variant(backend, nodes, names, pairing: bool, unpairing: bool):
    builder = builder_from_dag(backend, nodes, names)
    registers = [builder.reg(name) for name in REGISTERS]
    builder.sequence_lookup = {sequence.seq: i for i, sequence in enumerate(builder.sequences)}
    replacements, roots = {}, {}
    if pairing:
        head, tail, output = registers[6], registers[1], registers[7]
        loop = builder.while_decnz
        # Requires output = 0; consumes head and tail.
        body = [loop(tail, [output.inc, output.inc]), output.inc,
                loop(head, [loop(output, [tail.inc, tail.inc]), loop(tail, output.inc)])]
        root = builder.add_sequence(body)
        builder.sequences[root].name = "pair2adic().0"
        replacements[162], roots["pair"] = root, root
    if unpairing:
        for old, source in ((115, registers[8]), (116, registers[2])):
            head, tail = registers[6], registers[7]
            # An odd remainder exits outer with floor(source/2) in tail.
            odd = builder.label("test", [[source.decnz, "break_test"], "break_outer"])
            half = builder.label("halve", [source.decnz, [odd, [tail.inc, "continue_halve"]]])
            transfer = builder.label("transfer", [tail.decnz, [source.inc, "continue_transfer"]])
            outer = builder.label("outer", [half, [head.inc, [transfer, "continue_outer"]]])
            # Nil zero returns immediately, avoiding a divide-zero loop.
            root = builder.add_sequence([source.decnz, [source.inc, outer]])
            builder.sequences[root].name = f"unpair2adic{old}().0"
            replacements[old], roots[f"unpair{old}"] = root, root
    for i, sequence in enumerate(builder.sequences):
        if i not in replacements:
            sequence.seq = tuple(replacements.get(x, x) if isinstance(x, int) else x
                                 for x in sequence.seq)
    if pairing:
        # Existing formula tags are 4*C(head, tail)+tag. Rel(0,0) becomes 5.
        target = builder.add_sequence([registers[6].inc] * 5)
        builder.sequences[152].seq = (target, builder.sequences[152].seq[1])
    builder.reduce_to_cons()
    builder.name_sequences()
    return builder, roots


def execute_helper(builder, root, values, fuel=1000000):
    """Independent structured interpreter, without a TM or bignum shortcut."""
    remaining = [fuel]

    def run(edge):
        remaining[0] -= 1
        if remaining[0] < 0:
            raise RuntimeError("helper fuel exhausted")
        if isinstance(edge, int):
            while True:
                left, right = builder.sequences[edge].seq
                result = run(left)
                if result[0] == "break":
                    return ("normal",) if result[1] == 1 else ("break", result[1] - 1)
                if result[0] != "normal":
                    return result
                result = run(right)
                if result[0] == "continue":
                    if result[1] == 1:
                        continue
                    return ("continue", result[1] - 1)
                return result
        if edge.startswith("_break."):
            return "break", int(edge.split(".")[1])
        if edge.startswith("_continue."):
            return "continue", int(edge.split(".")[1])
        if edge == "halt":
            return ("halt",)
        _, name, kind = edge.split(".")
        register = REGISTERS.index(name)
        if kind == "inc":
            values[register] += 1
            return ("normal",)
        if values[register]:
            values[register] -= 1
            return ("normal",)
        return "break", 1

    return run(root)


def uncons(number):
    if number == 0:
        return 0, 0
    head = 0
    while number % 2 == 0:
        head += 1
        number //= 2
    return head, number // 2


def measure(backend, nodes, names):
    results = []
    for pairing, unpairing in ((False, False), (True, False), (False, True), (True, True)):
        builder, roots = variant(backend, nodes, names, pairing, unpairing)
        tests = 0
        if pairing:
            for head in range(7):
                for tail in range(8):
                    values = [0] * 9
                    values[6], values[1] = head, tail
                    result = execute_helper(builder, roots["pair"], values)
                    if (result != ("normal",) or values[7] != 2**head * (2*tail + 1)
                            or values[6] != 0 or values[1] != 0):
                        raise ValueError("2-adic pair contract failed")
                    tests += 1
        if unpairing:
            for key, source in (("unpair115", 8), ("unpair116", 2)):
                for number in range(257):
                    values = [0] * 9
                    values[source] = number
                    result = execute_helper(builder, roots[key], values)
                    if (result != ("normal",) or (values[6], values[7]) != uncons(number)
                            or values[source] != 0):
                        raise ValueError("2-adic unpair contract failed")
                    tests += 1
        builder.generate()
        builder.tm.gc()
        states = {state for state, _ in builder.tm.states}
        results.append({"pair_2adic": pairing, "unpair_2adic": unpairing,
                        "encoder_decoder_agree": pairing == unpairing,
                        "working_states": len(states),
                        "framework_states": sum(q[0].isdigit() for q in states),
                        "decision_states": sum(not q[0].isdigit() for q in states),
                        "helper_contract_cases_passed": tests,
                        "designated_formula_target": 5 if pairing else 1})
    return {"upstream_commit": COMMIT, "variants": results,
            "whole_program_or_Lean_verification_supplied": False,
            "new_ZFC_machine_or_state_bound_claimed": False,
            "conclusion": "Naive recursive 2-adic pairing increases this unary-register backend's state count."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream-clone", type=Path)
    parser.add_argument("--scratch", type=Path, required=True)
    parser.add_argument("--output-evidence", type=Path)
    args = parser.parse_args()
    scratch = args.scratch.resolve()
    if scratch == ROOT or ROOT in scratch.parents or scratch == Path("/"):
        parser.error("scratch must be outside the repository and not filesystem root")
    scratch.mkdir(parents=True, exist_ok=True)
    for name in ("TMBuilder.py", "tm.py", "tmdb.py", "LICENSE.wade"):
        (scratch / name).write_bytes(git_bytes(args.upstream_clone, "ZF/generator/" + name))
    nodes, names = parse_dag(git_bytes(args.upstream_clone, "ZF/m254/coq/prog/Dag254.v").decode())
    sys.path.insert(0, str(scratch))
    backend = importlib.import_module("TMBuilder")
    encoded = json.dumps(measure(backend, nodes, names), indent=2, sort_keys=True) + "\n"
    if args.output_evidence:
        args.output_evidence.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
