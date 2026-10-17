#!/usr/bin/env python3
"""Three prepared-frame diagnostics after the focused phase-mask screen.

Literal mutated-table prefixes are separate from ORIGINAL register-program
residual traces. No reached-from-blank, weak bisimulation, changed-runtime,
consistency or smaller-machine claim follows from these bounded probes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

import candidate252_independent_audit as candidate


ROOT = Path(__file__).resolve().parents[4]
SOURCE = "Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm"
PROGRAM = "lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v"
PROGRAM_SHA = "1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746"
PREPARED = (
    (113, 23, 8390, "1111111111", (0, 0, 0, 0, 1, 0, 0, 0, 0)),
    (34, 68, 8236, "11101010011", (0, 0, 0, 0, 0, 0, 1, 0, 0)),
    (204, 252, 8390, "1111111111", (0, 0, 0, 0, 1, 0, 0, 0, 0)),
)


def read_nodes(path):
    text = path.read_text().split("Definition p254_tab", 1)[1].split("[", 1)[1].split("].", 1)[0]
    edge = r"(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)"
    nodes = re.findall(r"\((" + edge + r"),\s*(" + edge + r")\)", text)
    assert len(nodes) == 6459
    return nodes


def decode(nodes, pc):
    """Exact zero-padded decoder walk; report any nonzero unconsumed suffix."""
    node, path = 0, ""
    for _ in range(len(nodes) + 1):
        bit = pc[len(path)] if len(path) < len(pc) else "0"
        path += bit
        op, *argument = nodes[node][int(bit)].split()
        if op == "CN":
            node = int(argument[0])
            continue
        return {"consumed": path, "operation": op,
                "argument": int(argument[0]) if argument else None,
                "clean": not any(bit == "1" for bit in pc[len(path):])}
    raise AssertionError("decoder fuel exhausted")


def parse_file(ones, header):
    cursor, end, values = header + 1, max(ones), []
    while cursor <= end:
        if cursor in ones:
            return None
        cursor += 1
        count = 0
        while cursor in ones:
            count += 1
            cursor += 1
        if count == 0:
            return None
        values.append(count - 1)
    return values


def frames(nodes, ones, head):
    """Inspect the full exterior and complete suffix, not just nine registers."""
    if not ones or {point for point in ones if point < head} != {head - 1}:
        return []
    found = []
    for header in sorted(point for point in ones if point >= head + 40):
        values = parse_file(ones, header)
        if values is None or len(values) < 9:
            continue
        pc = "".join("1" if point in ones else "0"
                     for point in range(head, header)).rstrip("0")
        decoded = decode(nodes, pc)
        frame = {"header": header, "gap_total": header - head, "pc": pc,
                 "decoded": decoded, "physical_primary": values[:9],
                 "spares": values[9:]}
        if decoded["clean"]:
            assert candidate.paint(pc, header - head, values[:9], values[9:], head) == ones
            frame["whole_tape_repaint_equal"] = True
        found.append(frame)
        if decoded["clean"]:
            return found
    return found[:3]


def literal_probe(table, nodes, recipe, fuel):
    dead, target, case_index, pc, logical = recipe
    physical = [logical[candidate.NEWPHYS.index(register)] for register in range(9)]
    spares = [0, 1, 0]
    ones = candidate.paint(pc, 40, physical, spares, 0)
    initial_ones = sorted(ones)
    state, head = 96, 0
    changed = {key: (write, move, target if following == dead else following)
               for key, (write, move, following) in table.items() if key[0] != dead}
    assert len(changed) == 502
    assert all(changed[key] == table[key] for key in candidate.BOX_PAIRS)
    assert all(changed[64, bit] == table[64, bit] for bit in (0, 1))
    expected = candidate.successor(pc, "CC", 2, None).rstrip("0")
    visits, outcome = [], None
    for tick in range(1, fuel + 1):
        if state == 254:
            outcome = {"status": "halt", "ticks": tick - 1}
            break
        write, direction, state = changed[state, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if direction == "R" else -1
        if state != 96:
            continue
        parsed = frames(nodes, ones, head)
        visits.append({"ticks": tick, "head": head, "frames": parsed,
                       "left_context_ok": {point for point in ones if point < head} == {head - 1},
                       "one_count": len(ones)})
        clean = [frame for frame in parsed if frame["decoded"]["clean"]]
        if clean:
            frame = clean[0]
            outcome = {"status": "clean_dispatch_frame", "ticks": tick, "head": head,
                       **frame, "same_primary": frame["physical_primary"] == physical,
                       "same_pc_as_source_CC2": frame["pc"] == expected}
            break
    if outcome is None:
        outcome = {"status": "fuel_cutoff", "ticks": fuel}
    return {"deleted": dead, "target": target, "prepared_source_case": case_index,
            "source_pc": pc, "logical_values": list(logical),
            "physical_values": physical, "spares": spares,
            "source_expected_pc": expected,
            "source_expected_continuation": decode(nodes, expected),
            "initial_whole_ones": initial_ones, "outcome": outcome,
            "dispatch_visits": visits[:10], "total_dispatch_visits": len(visits),
            "whole_ones_at_stop": sorted(ones)}


def inc_path(path):
    """RegisterPath.incPath preserves the carry's zero bits and path length."""
    if "0" not in path:
        return "0" * len(path)
    index = path.rindex("0")
    return path[:index] + "1" + "0" * (len(path) - index - 1)


def strip_path(path, bit, count):
    while path and count:
        count -= path[-1] == bit
        path = path[:-1]
    return path


def original_residual_trace(nodes, pc, registers, budget=40):
    """ORIGINAL RM semantics from a prepared PC, not subsequent mutated TM steps."""
    registers, trace = list(registers), []
    for tick in range(budget):
        decoded = decode(nodes, pc)
        assert decoded["clean"]
        path, op, argument = decoded["consumed"], decoded["operation"], decoded["argument"]
        trace.append({"step": tick, "finite_pc_bits": pc, "canonical_pc": pc.rstrip("0"),
                      **decoded, "registers": registers.copy()})
        if path == "000" and tick > 0:
            return {"status": "main_join", "trace": trace,
                    "registers_at_join": registers.copy()}
        if op == "CH":
            return {"status": "halt", "trace": trace}
        if op == "CI":
            registers[argument] += 1
            pc = inc_path(path)
        elif op == "CD":
            if registers[argument] == 0:
                pc = inc_path(strip_path(path, "0", 1))
            else:
                registers[argument] -= 1
                pc = inc_path(path)
        elif op == "CB":
            pc = inc_path(strip_path(path, "0", argument))
        elif op == "CC":
            pc = strip_path(path, "1", argument)
        else:
            raise AssertionError(op)
    return {"status": "fuel_cutoff", "trace": trace}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not __debug__:
        parser.error("Assertions must remain enabled")
    raw = (ROOT / SOURCE).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == candidate.EXPECTED_SHA
    assert hashlib.sha256((ROOT / PROGRAM).read_bytes()).hexdigest() == PROGRAM_SHA
    table, nodes = candidate.read_table(raw), read_nodes(ROOT / PROGRAM)
    probes = [literal_probe(table, nodes, recipe, 20000) for recipe in PREPARED]
    assert [probe["outcome"]["ticks"] for probe in probes] == [484, 504, 34]
    residuals = []
    for scratch in (0, 1, 2):
        registers = (0, 0, 0, 0, 1, 0, scratch, 0, 0)
        expected = original_residual_trace(nodes, "11111111", registers)
        alternate = original_residual_trace(nodes, "1111110111", registers)
        assert expected["registers_at_join"] == [0, 0, 0, 0, scratch + 1, 0, 0, 0, 0]
        assert alternate["registers_at_join"] == [0, 1, 0, 0, scratch + 1, 0, 0, 0, 0]
        residuals.append({"input_registers": list(registers),
                          "expected_original_residual": expected,
                          "alternate_original_residual": alternate})
    result = {"status": "three bounded literal probes and original-residual traces reproduced",
              "scope": __doc__, "command": [sys.executable, *sys.argv],
              "attribution": "Mira-Cult/Jeff/Wade original254; mira-emmy public253; ProveIt permutation252.",
              "source_sha256": {SOURCE: hashlib.sha256(raw).hexdigest(),
                                PROGRAM: hashlib.sha256((ROOT / PROGRAM).read_bytes()).hexdigest(),
                                str(Path(__file__).relative_to(ROOT)): hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                                str(Path(candidate.__file__).relative_to(ROOT)): hashlib.sha256(Path(candidate.__file__).read_bytes()).hexdigest()},
              "literal_fuel": 20000, "residual_fuel": 40, "probes": probes,
              "original_residual_comparison": residuals,
              "conclusion": "204→252 returns a different clean PC with unchanged file, but the two ORIGINAL residuals change different semantic fields: alternate adds initial p1>0 to tw. This is not a weak-bisimulation certificate or a continued-mutant execution claim."}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"],
                      "literal_ticks": [probe["outcome"]["ticks"] for probe in probes],
                      "original_residual_samples": len(residuals)}, indent=2))


if __name__ == "__main__":
    main()
