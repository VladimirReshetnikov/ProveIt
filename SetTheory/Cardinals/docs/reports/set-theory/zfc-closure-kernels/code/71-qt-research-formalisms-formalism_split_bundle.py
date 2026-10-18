#!/usr/bin/env python3
"""Build and audit a split-bundle source with one conditional four-slot scrub.

Matched public Wade backend measurements include its initializer, but are not
new consistency-machine bounds: the changed literal runtime and initialization
need their own proofs.  The new source-calculus transfer is proved separately.
The original source, compiler, and symbolic emitter remain attributed inputs.
"""
import importlib
import itertools
import json
import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REF = ROOT / "formalism_reference"
sys.path.insert(0, str(REF))
import emitter as d
import TMBuilder as backend

REGISTERS = ["nextproof", "topwff", "wffstack", "axiomcode", "param1",
             "param2", "scratch1", "scratch2", "prooflist"]
MACROS = {166, 121, 168, 171, 177, 119, 181, 182, 180, 218, 178, 183,
          176, 158, 208, 192, 131, 211, 197}


def read_dag():
    pattern = (r"\| ([0-9]+) => \((E\w+(?: [0-9]+)?), (E\w+(?: [0-9]+)?)\)"
               r"\s+\(\* (.*?) \*\)")
    nodes, names = {}, {}
    for match in re.finditer(pattern, (REF / "Dag254.v").read_text()):
        number, left, right, name = match.groups()
        nodes[int(number)] = (left, right)
        names[int(number)] = name
    assert set(nodes) == set(range(219)) and names[0] == "main().0"
    return nodes, names


def builder_from_dag(nodes, names):
    b = backend.TMBuilder()
    regs = [b.reg(name) for name in REGISTERS]

    def edge(text):
        if text == "EHalt":
            return "halt"
        kind, number = text.split()
        n = int(number)
        if kind == "ENode":
            return n
        if kind == "EInc":
            return regs[n].inc
        if kind == "EDecnz":
            return regs[n].decnz
        assert kind in ("EBreak", "EContinue")
        return f"_{'break' if kind == 'EBreak' else 'continue'}.{n}"

    for q in range(len(nodes)):
        sequence = backend.Sequence(tuple(edge(e) for e in nodes[q]))
        sequence.name = names[q]
        b.sequences.append(sequence)
    b.sequence_lookup = {s.seq: i for i, s in enumerate(b.sequences)}
    return b


def expand(nodes, root):
    if root in MACROS:
        return [root]
    result = []
    for edge in nodes[root]:
        kind, number = edge.split()
        assert kind == "ENode"
        result.extend(expand(nodes, int(number)))
    return result


def reuse(nodes, program):
    patterns = [(expand(nodes, q), q) for q in range(1, 115) if q not in MACROS]
    best = [None] * (len(program) + 1)
    best[-1] = []
    for i in reversed(range(len(program))):
        choices = [[program[i]] + best[i + 1]]
        for pattern, q in patterns:
            j = i + len(pattern)
            if program[i:j] == pattern:
                choices.append([q] + best[j])
        best[i] = min(choices, key=lambda xs: (len(xs), repr(xs)))
    return best[0]


def export_source(b):
    reachable = list(b.reachable())
    assert reachable[0] == 0
    reachable = [0] + sorted(set(reachable) - {0})
    renumber = {q: n for n, q in enumerate(reachable)}
    nodes, names = {}, {}
    for old in reachable:
        def edge(x):
            if isinstance(x, int):
                return f"ENode {renumber[x]}"
            if x == "halt":
                return "EHalt"
            if x.startswith("_break."):
                return "EBreak " + x.split(".")[1]
            if x.startswith("_continue."):
                return "EContinue " + x.split(".")[1]
            _, reg, action = x.split(".")
            assert action in ("inc", "decnz")
            return f"{'EInc' if action == 'inc' else 'EDecnz'} {REGISTERS.index(reg)}"
        q = renumber[old]
        assert len(b.sequences[old].seq) == 2
        nodes[q] = [edge(x) for x in b.sequences[old].seq]
        names[q] = b.sequences[old].name
    return {"nodes": nodes, "names": names, "registers": REGISTERS}


def check_edges(machine, source):
    byname = {name: q for q, name in source["names"].items()}
    count = 0
    for q, edges in source["nodes"].items():
        for bit, expected in enumerate(edges):
            action = machine.states[source["names"][q], str(bit)]
            target = action.nextstate
            if target in byname:
                actual = f"ENode {byname[target]}"
            elif target == "halt":
                actual = "EHalt"
            elif match := re.fullmatch(r"3\.(.*)\.(inc|decnz)", target):
                actual = (f"{'EInc' if match[2] == 'inc' else 'EDecnz'} "
                          f"{REGISTERS.index(match[1])}")
            elif target.startswith("6.break."):
                actual = f"EBreak {int(target.rsplit('.', 1)[1]) + (bit == 0)}"
            else:
                assert target.startswith("6.continue."), target
                level = int(target.rsplit(".", 1)[1])
                actual = ("EBreak 0" if bit == 0 and action.write == "1"
                          else f"EContinue {level + bit}")
            assert actual == expected, (q, bit, actual, expected)
            direct = expected.split()[0] in ("ENode", "EInc", "EDecnz", "EHalt")
            write = str(bit) if direct else ("1" if expected == "EBreak 0" and bit == 0 else "0")
            assert action.write == write and action.direction == ("R" if direct else "L")
            count += 1
    return count


def execute(b, root, registers, fuel=5000000):
    """Literal structured register interpreter with no helper shortcuts."""
    used = 0

    def run(edge):
        nonlocal used
        used += 1
        assert used <= fuel, "register execution fuel exhausted"
        if isinstance(edge, int):
            while True:
                left, right = b.sequences[edge].seq
                kind, level = run(left)
                if kind == "break":
                    return ("normal", 0) if level == 1 else (kind, level - 1)
                if kind != "normal":
                    return kind, level
                kind, level = run(right)
                if kind == "continue":
                    if level == 1:
                        continue
                    return kind, level - 1
                return kind, level
        if edge.startswith("_break."):
            return "break", int(edge.split(".")[1])
        if edge.startswith("_continue."):
            return "continue", int(edge.split(".")[1])
        assert edge != "halt", "helper halted"
        _, name, action = edge.split(".")
        index = REGISTERS.index(name)
        if action == "inc":
            registers[index] += 1
            return "normal", 0
        assert action == "decnz"
        if registers[index]:
            registers[index] -= 1
            return "normal", 0
        return "break", 1

    assert run(root) == ("normal", 0)
    return used


def pair(x, y):
    return (x + y) * (x + y + 1) // 2 + y


def stack3(x, y, z, tail):
    return pair(x, pair(y, pair(z, tail)))


def build(nodes, names, mode):
    b = builder_from_dag(nodes, names)
    if mode == "original":
        return b, {}, None
    spec = d.load_spec()
    rows = spec["ax_rows"]("a", "old_cache", "b", "c", "u")
    logical = [166, 121, 180, 176] + [m for f in rows[1:] for m in d.emit(f)]
    if mode == "reemit":
        program = logical + d.emit(spec["bundle"]("a", "b", "c")) + d.TAIL
        assert program == expand(nodes, 1)
        roots = {}
    else:
        r = [b.reg(name) for name in REGISTERS]
        clear_head = b.while_decnz(r[6], ())
        pop_discard = b.add_sequence([116, 212, clear_head])
        b.sequences[pop_discard].name = "formalism_pop_discard().0"
        scrub = b.add_sequence([pop_discard] * 3 + [171] * 3)
        b.sequences[scrub].name = "formalism_scrub4().0"
        conditional = b.add_sequence(b.label("zero_scrub", [
            [r[1].decnz, [r[1].inc, "break_zero_scrub"]], scrub]))
        b.sequences[conditional].name = "formalism_conditional_scrub().0"
        C = spec["bundle_C"]("a", "b", "c")
        G = spec["bundle_G"]("a", "b", "c")
        VR = d.imp(("rel", "a", "b"), ("all", "c", ("rel", "a", "b")))
        VE = d.imp(("eq", "a", "b"), ("all", "c", ("eq", "a", "b")))
        # VE is always a strictly positive implication code.  It is the gate
        # sentinel; do not permute it out of the final position unconditionally.
        components = [C, G, VR, VE]
        program = logical + [m for f in components for m in d.emit(f)] + d.TAIL + [conditional]
        symbolic, events = d.execute_macros(program[:-len(d.TAIL)-1])
        assert symbolic == ["old_top"] + rows + components
        assert events == [(176, 2), (158, 4)]
        roots = {"pop_discard": pop_discard, "scrub": scrub, "conditional": conditional}
        gate_and_scrub = b.add_sequence(d.TAIL + [conditional])
        b.sequences[gate_and_scrub].name = "formalism_gate_and_scrub().0"
        roots["gate_and_scrub"] = gate_and_scrub
    root = b.add_sequence(reuse(nodes, program))
    b.sequences[root].name = f"formalism_AX_{mode}().0"
    for i, seq in enumerate(b.sequences):
        if i != 1:
            seq.seq = tuple(root if child == 1 else child for child in seq.seq)
    if mode == "split_shared":
        b.breakout_common_subsequences()
    b.reduce_to_cons()
    b.name_sequences()
    return b, roots, program


def test_helpers(b, roots):
    count, maximum = 0, 0
    for x, y, z, tail in itertools.product(range(2), repeat=4):
        initial = [7, 0, stack3(x, y, z, tail), 0, 11, 0, 0, 0, 13]
        wanted = list(initial)
        wanted[2] = stack3(0, 0, 0, tail)
        actual = list(initial)
        maximum = max(maximum, execute(b, roots["scrub"], actual))
        assert actual == wanted
        count += 1
        for top in (1, 4, 9):
            actual = list(initial)
            actual[1] = top
            wanted = list(actual)
            maximum = max(maximum, execute(b, roots["conditional"], actual))
            assert actual == wanted
            count += 1
    for a, bval, c, tail in itertools.product(range(4), range(4), range(4), range(2)):
        initial = [7, 4, stack3(1, 0, 1, tail), c, a, bval, 0, 0, 13]
        wanted = list(initial)
        wanted[3:8] = [0] * 5
        if c == a or c == bval:
            wanted[1] = 0
            wanted[2] = stack3(0, 0, 0, tail)
        actual = list(initial)
        maximum = max(maximum, execute(b, roots["gate_and_scrub"], actual))
        assert actual == wanted, (a, bval, c, tail, actual, wanted)
        count += 1
    return {"cases": count, "maximum_interpreter_edge_calls": maximum,
            "all_registers_checked": True}


def write_tm(machine, filename):
    states = {q for q, bit in machine.states}
    start = machine.start
    assert start in states
    order = [start] + sorted(states - {start})
    numbering = {q: i for i, q in enumerate(order)}
    halt = len(order)
    assert {a.nextstate for a in machine.states.values()} - states == {"halt"}
    lines = ["# Public Wade compiler measurement; not a certified consistency-machine record.",
             "# state read write direction next_state; start 0; halt " + str(halt)]
    missing = []
    for q in order:
        for bit in ("0", "1"):
            action = machine.states.get((q, bit))
            if action is None:
                assert q == "1.inc" and bit == "1"
                missing.append([q, bit])
                write, direction, target = bit, "R", halt
            else:
                write, direction = action.write, action.direction
                target = numbering.get(action.nextstate, halt)
            lines.append(f"{numbering[q]} {bit} {write} {direction} {target}")
    filename.write_text("\n".join(lines) + "\n")
    return {"working_states": halt, "rows": 2 * halt,
            "totalized_missing_rows": missing,
            "sha256": hashlib.sha256(filename.read_bytes()).hexdigest()}


def main():
    nodes, names = read_dag()
    results = {}
    for mode in ("original", "reemit", "split", "split_shared"):
        b, roots, program = build(nodes, names, mode)
        checks = test_helpers(b, roots) if roots else None
        source = export_source(b)
        b.generate()
        b.tm.gc()
        source_edges = check_edges(b.tm, source)
        prefix = ROOT / f"formalism_split_{mode}"
        (prefix.with_suffix(".source.json")).write_text(json.dumps(source, indent=2) + "\n")
        if program is not None:
            (prefix.with_suffix(".emission.json")).write_text(json.dumps({"word": program,
                "helper_roots_before_reindex": roots}, indent=2) + "\n")
        measured = write_tm(b.tm, prefix.with_suffix(".tm"))
        measured.update({"decision_states": len(source["nodes"]),
            "framework_states": measured["working_states"] - len(source["nodes"]),
            "source_edges_reextracted": source_edges, "helper_checks": checks})
        results[mode] = measured
        print(mode, json.dumps(measured), flush=True)
    assert results["original"]["working_states"] == results["reemit"]["working_states"] == 281
    report = {"scope": "Complete public-backend table measurements and source-helper audits; no new binary simulation or bootstrap theorem.",
              "results": results, "status": "PASS"}
    (ROOT / "formalism_split_results.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
