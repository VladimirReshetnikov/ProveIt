"""Assemble a fresh binary TM using Mira-Cult's published single-marker engine.

Only pinned finite data is read from the immutable vendored snapshot. No
upstream Python or Coq code is executed. The generated initializer is charged
in full; the source-specific 254-machine bootstrap is deliberately replaced.
This is an executable assembler experiment, without a Lean simulation theorem
or a consistency calibration for its output. See mira_backend.md.

Offline reproduction:
  python3 Computability/BusyBeaver/Research/ZFC/mira_backend.py \
    --scratch /tmp/zfc-mira-backend --output-evidence /tmp/mira-results.json
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import random
import re
from types import SimpleNamespace

from recover_wade_dag import COMMIT, REGISTERS, ROOT, SNAPSHOT, git_bytes, parse_dag

LITERAL_PATH = "ZF/m254/machine/zfc_254.tm"
LITERAL_SHA256 = "d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb"
DAG_PATH = "ZF/m254/coq/prog/Dag254.v"
PHYS_ORDER = (2, 4, 3, 7, 6, 8, 0, 1, 5)
PHYS_OF = (6, 7, 0, 2, 1, 8, 4, 3, 5)
SKIP = (60, 44, 31, 56, 38, 40, 28, 64, 69)
COUNTER = (4, 6, 9, 13, 19, 29, 41, 58, 74)
CORE = (0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 13, 14, 19, 20, 28, 29,
        30, 31, 38, 40, 41, 42, 43, 44, 48, 56, 57, 58, 59, 60,
        63, 64, 69, 73, 74, 75, 83, 84, 85, 95, 97, 109, 112, 131)
Action = tuple[int, str, int]
Table = dict[tuple[int, int], Action]


def pinned_literal() -> Table:
    data = (SNAPSHOT / LITERAL_PATH).read_bytes()
    if hashlib.sha256(data).hexdigest() != LITERAL_SHA256:
        raise ValueError("literal table differs from the pinned source")
    table = {}
    for line in data.decode().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        q, b, w, direction, target = line.split()
        key = int(q), int(b)
        if key in table or direction not in ("L", "R"):
            raise ValueError("malformed literal table")
        table[key] = int(w), direction, int(target)
    if set(table) != {(q, b) for q in range(254) for b in (0, 1)}:
        raise ValueError("incomplete literal table")
    return table


def parse_edge(edge: str) -> tuple[str, int | None]:
    if edge == "EHalt":
        return "EHalt", None
    match = re.fullmatch(r"(ENode|EInc|EDecnz|EBreak|EContinue) ([0-9]+)", edge)
    if match is None:
        raise ValueError(f"unsupported edge: {edge!r}")
    kind, number = match.groups()
    n = int(number)
    if kind in ("EInc", "EDecnz") and n >= 9:
        raise ValueError("this engine supports exactly nine register positions")
    return kind, n


def instruction_sites(nodes: dict[int, tuple[str, str]]) -> list[tuple[str, str]]:
    """Unfold a finite DAG, checking control levels at every occurrence."""
    if 0 not in nodes:
        raise ValueError("DAG root must be node 0")
    sites = []

    def walk(q, path, ancestors):
        if q in ancestors:
            raise ValueError("decoder graph is cyclic")
        if q not in nodes or len(nodes[q]) != 2:
            raise ValueError("missing node or nonbinary sequence")
        for b, edge in enumerate(nodes[q]):
            p = path + str(b)
            kind, n = parse_edge(edge)
            if kind == "ENode":
                walk(n, p, ancestors | {q})
            else:
                if kind == "EDecnz" and "0" not in p:
                    raise ValueError("zero decrement can escape the root")
                if kind in ("EBreak", "EContinue"):
                    bit = "0" if kind == "EBreak" else "1"
                    if n > p.count(bit):
                        raise ValueError(f"{edge} can escape the root at {p}")
                sites.append((p, edge))

    walk(0, "", set())
    return sites


def inc_path(path: str) -> tuple[str, bool]:
    if "0" not in path:
        return "", True
    return path[:path.rindex("0")] + "1", False


def strip_path(bit: str, level: int, path: str) -> str:
    while level:
        if not path:
            raise ValueError("control escapes the root")
        if path[-1] == bit:
            level -= 1
        path = path[:-1]
    return path


def seps(values: list[int] | tuple[int, ...], mark: int | None = None) -> list[int]:
    return [bit for r, value in enumerate(values)
            for bit in [0, 0 if r == mark else 1] + [1] * value]


@dataclass
class MiraMachine:
    table: Table
    labels: dict[str, int]
    sites: list[tuple[str, str]]
    evidence: dict
    gap: int
    initial_registers: tuple[int, ...]

    @property
    def halt(self) -> int:
        return len(self.table) // 2

    @property
    def root(self) -> int:
        return self.labels["d:0"]

    def encoded(self) -> bytes:
        lines = ["#! start 0"]
        for q in range(self.halt):
            for b in (0, 1):
                w, direction, target = self.table[q, b]
                lines.append(f"{q} {b} {w} {direction} {target}")
        return ("\n".join(lines) + "\n").encode()

    def save(self, path: str | Path) -> None:
        path = Path(path).resolve()
        if path == ROOT or ROOT in path.parents:
            raise ValueError("generated tables must be saved outside the repository")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(self.encoded())

    def check_sites(self) -> dict:
        counts = Counter()
        max_steps = max_visits = 0
        for path, edge in self.sites:
            kind, register = parse_edge(edge)
            branches = (True, False) if kind == "EDecnz" else (None,)
            for zero in branches:
                steps, visits = symbolic_site(self, path, edge, zero)
                counts[kind + ("/zero" if zero is True else
                               "/positive" if zero is False else "")] += 1
                max_steps = max(max_steps, steps)
                max_visits = max(max_visits, visits)
        result = {"cases_passed": sum(counts.values()),
                  "cases_by_operation": dict(sorted(counts.items())),
                  "max_symbolic_steps": max_steps, "max_dispatch_visits": max_visits,
                  "arbitrary_gap_parameter_and_register_box": True,
                  "formal_proof": False}
        self.evidence["symbolic_site_checks"] = result
        return result


def compile_dag(nodes: dict[int, tuple[str, str]], names: dict[int, str] | None = None,
                *, initial_registers=None, gap: int | None = None,
                dispatcher_threshold: int | None = None,
                generic_decrement: bool = True,
                initializer: str = "direct") -> MiraMachine:
    """Compile RM edges to a total binary table with start0 and halt=N.

    Defaults start all nine logical registers at zero. Pass [2,0,...,0] to
    match the published post-boot register vector instead. No old boot is used.
    Names are metadata only. Unreachable source nodes are discarded.
    initializer='compact' uses source21's counted counter/stride construction;
    gap then specifies a minimum and may round up to the chosen exact gap.
    """
    sites = instruction_sites(nodes)
    depth = max(len(p) for p, _ in sites)
    zero_run = max(max(map(len, p.split("1"))) for p, _ in sites)
    gap = depth + 6 if gap is None else gap
    threshold = (max(9, zero_run + 2) if dispatcher_threshold is None
                 else dispatcher_threshold)
    if type(gap) is not int or type(threshold) is not int:
        raise ValueError("gap and dispatcher threshold must be integers")
    if gap < depth + 6:
        raise ValueError("gap must leave at least six cells after the deepest leaf")
    if initializer not in ("direct", "compact"):
        raise ValueError("initializer must be direct or compact")
    minimum_gap = gap
    if initializer == "compact":
        from compact_initializer import choose_parameters, make_initializer
        counters, stride = choose_parameters(gap)
        gap = counters * (stride + 2) + 2
    if threshold < max(9, zero_run + 2):
        raise ValueError("dispatcher threshold does not cover path/phase zero runs")
    if not generic_decrement and any(e.startswith("EDecnz") and not p.endswith("0")
                                     for p, e in sites):
        raise ValueError("unpatched zero return requires decrement paths ending0")
    initial = tuple([0] * 9 if initial_registers is None else initial_registers)
    if len(initial) != 9 or any(type(n) is not int or n < 0 for n in initial):
        raise ValueError("initial_registers must contain nine natural numbers")
    literal = pinned_literal()
    labeled = {}

    def put(label, b, w, direction, target):
        if (label, b) in labeled:
            raise ValueError(f"duplicate generated row {label}/{b}")
        labeled[label, b] = w, direction, target

    def engine(q):
        return "d:0" if q == 96 else "halt" if q == 254 else f"e:{q}"

    for q in CORE:
        for b in (0, 1):
            w, direction, target = literal[q, b]
            if q == 5 and b == 1:
                # This branch formerly entered the source-specific bootstrap.
                w, direction = 0, "L"
                target_label = "b:1" if generic_decrement else "halt"
            else:
                target_label = engine(target)
            put(engine(q), b, w, direction, target_label)
    if threshold > 9:
        labeled[engine(74), 0] = 0, "L", "z:9"
        for count in range(9, threshold):
            put(f"z:{count}", 1, 1, "L", engine(4))
            target = f"z:{count+1}" if count+1 < threshold else engine(84)
            put(f"z:{count}", 0, 0, "L" if count+1 < threshold else "R", target)

    reachable = set()

    def collect(q):
        if q in reachable:
            return
        reachable.add(q)
        for e in nodes[q]:
            kind, n = parse_edge(e)
            if kind == "ENode":
                collect(n)

    collect(0)
    leaves = {e for q in reachable for e in nodes[q] if not e.startswith("ENode")}
    break_levels = [parse_edge(e)[1] for e in leaves if e.startswith("EBreak")]
    max_break = max(break_levels + [1 if generic_decrement else 0])
    for k in range(1, max_break + 1):
        put(f"b:{k}", 1, 0, "L", f"b:{k}")
        put(f"b:{k}", 0, 0, "L", engine(7) if k == 1 else f"b:{k-1}")
    continue_levels = [parse_edge(e)[1] for e in leaves if e.startswith("EContinue")]
    for k in range(1, max(continue_levels + [0]) + 1):
        put(f"c:{k}", 0, 0, "L", f"c:{k}")
        put(f"c:{k}", 1, 0, "R" if k == 1 else "L",
            engine(10) if k == 1 else f"c:{k-1}")

    def leaf_label(edge):
        kind, n = parse_edge(edge)
        if kind == "EHalt":
            return "halt"
        if kind == "ENode":
            return f"d:{n}"
        if kind == "EContinue" and n:
            return f"c:{n}"
        return f"l:{edge}"

    for edge in sorted(leaves):
        kind, n = parse_edge(edge)
        label = leaf_label(edge)
        if kind in ("EInc", "EDecnz"):
            put(label, 0, 0, "R", engine(57 if kind == "EInc" else 30))
            put(label, 1, 0, "R", engine(SKIP[PHYS_OF[n]]))
        elif kind == "EBreak":
            for b in (0, 1):
                put(label, b, b, "L", f"b:{n}" if n else engine(7))
        elif kind == "EContinue" and n == 0:
            for b in (0, 1):
                put(label, b, 0, "R", engine(10))
    for q in sorted(reachable):
        for b, edge in enumerate(nodes[q]):
            put(f"d:{q}", b, b, "R", leaf_label(edge))

    compact_contract = None
    if initializer == "compact":
        initial_rows, compact_contract = make_initializer(initial, counters, stride, "d:0")
        for (label, bit), (write, direction, target) in initial_rows.items():
            put(label, bit, write, direction, target)
        initializer_steps = compact_contract["blank_steps"]
    else:
        physical_initial = [initial[i] for i in PHYS_ORDER]
        wire = list(reversed(seps(physical_initial))) + [1] + [0] * gap + [1]
        for i, bit in enumerate(wire):
            last = i+1 == len(wire)
            for b in (0, 1):
                put(f"i:{i}", b, bit, "R" if last else "L",
                    "d:0" if last else f"i:{i+1}")
        initializer_steps = len(wire)

    # Syntactic reachability charges both rows, including invariant-unused rows.
    live = set()
    todo = ["i:0"]
    while todo:
        q = todo.pop()
        if q == "halt" or q in live:
            continue
        live.add(q)
        for b in (0, 1):
            if (q, b) not in labeled:
                raise ValueError(f"generated target has no complete row: {q}/{b}")
            todo.append(labeled[q, b][2])
    order = ["i:0"] + sorted(live - {"i:0"})
    labels = {name: q for q, name in enumerate(order)}
    labels["halt"] = len(order)
    table = {(labels[q], b): (w, direction, labels[target])
             for (q, b), (w, direction, target) in labeled.items() if q in live}
    categories = Counter(q.split(":", 1)[0] for q in live)
    evidence = {"upstream_commit": COMMIT, "literal_source": LITERAL_PATH,
                "literal_sha256": LITERAL_SHA256, "input_DAG_nodes": len(nodes),
                "reachable_DAG_nodes": len(reachable), "instruction_sites": len(sites),
                "max_path_depth": depth, "max_path_zero_run": zero_run,
                "gap": gap, "dispatcher_threshold": threshold,
                "generic_decrement_patch": generic_decrement,
                "initial_logical_registers": list(initial),
                "initializer_kind": initializer, "initializer_steps": initializer_steps,
                "requested_minimum_gap": minimum_gap,
                "working_states": len(order), "transition_rows": len(table),
                "states_by_role": {"initializer": categories["i"],
                                   "decoder": categories["d"], "literal_engine": categories["e"],
                                   "arithmetic_and_control_leaves": categories["l"],
                                   "break_scans": categories["b"],
                                   "continue_scans": categories["c"],
                                   "extended_dispatcher": categories["z"]},
                "fresh_initializer_charged": True, "source_py_required": False,
                "original_boot_reused": False, "original_optimizer_reconstructed": False,
                "Lean_simulation_proved": False, "consistency_calibration_proved": False,
                "new_ZFC_state_bound_claimed": False,
                "input_DAG_sha256": hashlib.sha256(json.dumps(
                    {str(q): list(nodes[q]) for q in sorted(nodes)}, sort_keys=True).encode()).hexdigest(),
                "root_name": (names or {}).get(0)}
    if compact_contract is not None:
        evidence["compact_initializer_contract"] = compact_contract
    machine = MiraMachine(table, labels, sites, evidence, gap, initial)
    evidence["machine_sha256"] = hashlib.sha256(machine.encoded()).hexdigest()
    return machine


def compile_builder(builder, **kwargs) -> MiraMachine:
    """Compile an already binary Wade builder without modifying it.

    Register names must use the declared nine-register interface. No upstream
    generate() call or upstream bootstrap is involved.
    """
    nodes, names = {}, {}
    for q, sequence in enumerate(builder.sequences):
        if len(sequence.seq) != 2:
            raise ValueError("call builder.reduce_to_cons() before compile_builder")
        edges = []
        for edge in sequence.seq:
            if type(edge) is int:
                encoded = f"ENode {edge}"
            elif edge == "halt":
                encoded = "EHalt"
            elif match := re.fullmatch(r"3\.(.+)\.(inc|decnz)", edge):
                if match[1] not in REGISTERS:
                    raise ValueError(f"unknown register {match[1]}")
                kind = "EInc" if match[2] == "inc" else "EDecnz"
                encoded = f"{kind} {REGISTERS.index(match[1])}"
            elif match := re.fullmatch(r"_(break|continue)\.([0-9]+)", edge):
                encoded = f"{'EBreak' if match[1] == 'break' else 'EContinue'} {match[2]}"
            else:
                raise ValueError(f"unsupported builder leaf {edge!r}")
            edges.append(encoded)
        nodes[q], names[q] = tuple(edges), sequence.name
    return compile_dag(nodes, names, **kwargs)


def canon_side(segments, left=False):
    out = []
    for segment in segments:
        if segment[0] == "box":
            out.append(segment)
            continue
        b, a, c = (segment[1], 0, 1) if segment[0] == "b" else segment[1:]
        if (a, c) == (0, 0):
            continue
        if out and out[-1][0] == b:
            out[-1] = b, out[-1][1] + a, out[-1][2] + c
        else:
            out.append((b, a, c))
    if left:
        while out and out[-1][0] == 0:
            out.pop()
    return tuple(out)


def symbolic_site(machine: MiraMachine, path: str, edge: str,
                  zero: bool | None, fuel=20000) -> tuple[int, int]:
    """Affine-run checker with four explicit register-box excursion rules.

    A run has a*n+c cells for arbitrary n>=0. Box rules stand for the cited
    published contracts, and are additionally exercised by concrete tests.
    This Python checker has no formal soundness theorem.
    """
    kind, n = parse_edge(edge)
    effects = ()
    if kind == "EInc" or kind == "EDecnz" and not zero:
        target_path, overflow = inc_path(path)
        effects = (("inc" if kind == "EInc" else "dec", PHYS_OF[n]),)
    elif kind in ("EDecnz", "EBreak"):
        target_path, overflow = inc_path(strip_path("0", 1 if kind == "EDecnz" else n, path))
    elif kind == "EContinue":
        target_path, overflow = strip_path("1", n, path), False
    else:
        target_path, overflow = "", False

    def right(p, extra=0, eff=()):
        return [("b", int(b)) for b in p] + [
            ("r", 0, 1, machine.gap + extra - len(p)), ("b", 1), ("box", ("plain", eff))]

    expected = canon_side([("b", 1)], True), canon_side(right(target_path, int(overflow), effects))
    q, form, left, rgt = machine.root, "c", [("b", 1)], right(path)
    steps = visits = 0
    skip = {machine.labels[f"e:{s}"]: r for r, s in enumerate(SKIP)
            if f"e:{s}" in machine.labels}

    def eng(k):
        return machine.labels[f"e:{k}"]

    for _ in range(fuel):
        if q == machine.halt:
            if kind != "EHalt":
                raise ValueError(f"unexpected halt at {path}/{edge}/{zero}")
            return steps, visits
        if form == "c" and q == machine.root:
            visits += 1
            if steps and (canon_side(left, True), canon_side(rgt)) == expected:
                if kind == "EHalt":
                    raise ValueError("halt site returned to dispatch")
                return steps, visits
        if form == "l":
            if not left:
                rgt = [("b", 0)] + rgt
                form = "c"
                continue
            seg = left[0]
            if seg[0] == "b":
                left, rgt, form = left[1:], [seg] + rgt, "c"
                continue
            _, b, a, c = seg
            w, direction, target = machine.table[q, b]
            if direction == "L" and target == q:
                left, rgt = left[1:], [("r", w, a, c)] + rgt
                steps += 1
                continue
            if c >= 1:
                left = ([("r", b, a, c-1)] if (a, c-1) != (0, 0) else []) + left[1:]
                rgt, form = [("b", b)] + rgt, "c"
                continue
            if a == 0:
                left = left[1:]
                continue
            raise ValueError(f"cannot peel left symbolic run at {path}/{edge}/{q}")
        if not rgt:
            raise ValueError("unexpected right exterior")
        seg = rgt[0]
        if seg[0] == "b":
            w, direction, target = machine.table[q, seg[1]]
            if direction == "R":
                left, rgt = [("b", w)] + left, rgt[1:]
            else:
                rgt, form = [("b", w)] + rgt[1:], "l"
            q, steps = target, steps + 1
            continue
        if seg[0] == "r":
            _, b, a, c = seg
            w, direction, target = machine.table[q, b]
            if direction == "R" and target == q:
                left, rgt = [("r", w, a, c)] + left, rgt[1:]
                steps += 1
                continue
            if c >= 1:
                rgt = [("b", b)] + ([("r", b, a, c-1)] if (a, c-1) != (0, 0) else []) + rgt[1:]
                continue
            if a == 0:
                rgt = rgt[1:]
                continue
            raise ValueError(f"cannot peel right symbolic run at {path}/{edge}/{q}")
        box = seg[1]
        if q in skip and box[0] == "plain":
            r = skip[q]
            rgt = [("box", ("mark", r, box[1]))]
            q, form, steps = eng(2 if r == 0 else 6), "l", steps + 1
            continue
        if box[0] == "mark" and q in (machine.labels.get("e:73"), machine.labels.get("e:43")):
            r, old_effects = box[1:]
            if q == machine.labels.get("e:73"):
                eff, target = old_effects + (("inc", r),), eng(48)
            else:
                if kind != "EDecnz" or r != PHYS_OF[n] or zero is None:
                    raise ValueError("decrement oracle branch/register mismatch")
                eff = old_effects if zero else old_effects + (("dec", r),)
                target = eng(3 if zero else 63 if r == 0 else 48)
            rgt = [("box", ("plain", eff))]
            q, form, steps = target, "l", steps + 1
            continue
        w, direction, target = machine.table[q, 0]
        if w == 0 and direction == "L":
            q, form, steps = target, "l", steps + 1
            continue
        raise ValueError(f"unexpected box access at {path}/{edge}/{q}")
    raise ValueError(f"symbolic fuel exhausted at {path}/{edge}/{zero}")


def concrete_step(machine, state, tape, head):
    w, direction, target = machine.table[state, tape.get(head, 0)]
    if w:
        tape[head] = 1
    else:
        tape.pop(head, None)
    return target, head + (1 if direction == "R" else -1)


def initial_configuration_check(machine: MiraMachine) -> dict:
    q, head, tape, steps = 0, 0, {}, 0
    expected_steps = machine.evidence.get(
        "initializer_steps", machine.evidence["states_by_role"]["initializer"])
    while q != machine.root:
        q, head = concrete_step(machine, q, tape, head)
        steps += 1
        if steps > expected_steps:
            raise ValueError("initializer did not reach dispatch")
    bits = [1] + [0] * machine.gap + [1] + seps([machine.initial_registers[i] for i in PHYS_ORDER])
    expected = {head-1+i: 1 for i, b in enumerate(bits) if b}
    expected_head = -(18 + sum(machine.initial_registers) + machine.gap)
    if tape != expected or steps != expected_steps or head != expected_head:
        raise ValueError("fresh initializer configuration differs")
    return {"passed": True, "concrete_steps": steps,
            "head": head, "nonzero_cells": len(tape),
            "register_blocks": 9, "spare_zero_blocks": 0}


def box_checks(machine: MiraMachine, trials=32) -> dict:
    rng, counts = random.Random(254), Counter()
    for trial in range(trials):
        values = [rng.choice((0, 0, 1, 2, 4)) for _ in range(9 + trial % 4)]
        for r in range(9):
            for operation in ("mark", "inc", "dec"):
                before = seps(values, None if operation == "mark" else r)
                tape = {i: 1 for i, b in enumerate(before) if b}
                tape[-1] = 1
                q = machine.labels[f"e:{SKIP[r] if operation == 'mark' else 73 if operation == 'inc' else 43}"]
                head, steps = 0, 0
                while head >= 0:
                    q, head = concrete_step(machine, q, tape, head)
                    steps += 1
                    if steps > 100000:
                        raise ValueError("box excursion fuel exhausted")
                after = values.copy()
                if operation == "mark":
                    expected = seps(after, r)
                    exit_state = 2 if r == 0 else 6
                elif operation == "inc":
                    after[r] += 1
                    expected, exit_state = seps(after), 48
                elif after[r] == 0:
                    expected, exit_state = seps(after), 3
                else:
                    after[r] -= 1
                    after.append(0)
                    expected, exit_state = seps(after), 63 if r == 0 else 48
                expected_tape = {i: 1 for i, b in enumerate(expected) if b} | {-1: 1}
                if tape != expected_tape or head != -1 or q != machine.labels[f"e:{exit_state}"]:
                    raise ValueError(f"concrete box contract failed: {operation}/{r}")
                counts[operation] += 1
    return {"cases_passed": sum(counts.values()), "by_operation": dict(counts),
            "seed": 254, "trials": trials, "formal_proof": False}


def concrete_site_checks(machine: MiraMachine, samples=40) -> dict:
    rng, cases, max_steps = random.Random(219), 0, 0
    # Cover each operation/register/level first, then uniformly spaced paths.
    selected = {}
    for p, e in machine.sites:
        selected.setdefault(e, (p, e))
    for i in range(min(samples, len(machine.sites))):
        p, e = machine.sites[i * len(machine.sites) // min(samples, len(machine.sites))]
        selected[(p, e)] = (p, e)
    for path, edge in selected.values():
        kind, n = parse_edge(edge)
        for zero in ((True, False) if kind == "EDecnz" else (None,)):
            values = [rng.randrange(4) for _ in range(9)] + [0, 2]
            after = values.copy()
            if kind == "EDecnz":
                values[PHYS_OF[n]] = after[PHYS_OF[n]] = 0 if zero else 2
            if kind == "EInc" or kind == "EDecnz" and not zero:
                target, overflow = inc_path(path)
                after[PHYS_OF[n]] += 1 if kind == "EInc" else -1
                if kind == "EDecnz":
                    after.append(0)
            elif kind in ("EDecnz", "EBreak"):
                target, overflow = inc_path(strip_path("0", 1 if kind == "EDecnz" else n, path))
            elif kind == "EContinue":
                target, overflow = strip_path("1", n, path), False
            else:
                target, overflow = "", False
            extra = cases % 3
            before_bits = [1] + list(map(int, path)) + [0] * (machine.gap + extra - len(path)) + [1] + seps(values)
            tape = {i-1: 1 for i, b in enumerate(before_bits) if b}
            offset = -int(overflow)
            after_bits = [1] + list(map(int, target)) + [0] * (machine.gap + extra + int(overflow) - len(target)) + [1] + seps(after)
            expected = {offset+i-1: 1 for i, b in enumerate(after_bits) if b}
            q, head, steps = machine.root, 0, 0
            while steps < 2000000:
                q, head = concrete_step(machine, q, tape, head)
                steps += 1
                if q == machine.halt:
                    if kind != "EHalt":
                        raise ValueError("concrete instruction halted unexpectedly")
                    break
                if q == machine.root and head == offset and tape == expected:
                    if kind == "EHalt":
                        raise ValueError("concrete halt site returned")
                    break
            else:
                raise ValueError(f"concrete instruction fuel exhausted: {path}/{edge}")
            max_steps = max(max_steps, steps)
            cases += 1
    return {"cases_passed": cases, "max_concrete_steps": max_steps, "seed": 219,
            "extra_gap_values": [0, 1, 2], "formal_proof": False}


def offline_regressions() -> dict:
    programs = [({0: ("EHalt", "EHalt")}, [0] * 9),
                ({0: ("EInc 0", "EHalt")}, [0] * 9),
                ({0: ("ENode 1", "EHalt"), 1: ("EDecnz 0", "EContinue 1")}, [2] + [0] * 8),
                ({0: ("ENode 1", "EHalt"), 1: ("ENode 2", "EContinue 1"),
                  2: ("EInc 1", "EDecnz 0")}, [2] + [0] * 8)]
    checks = symbolic_cases = builder_roundtrips = 0
    for nodes, initial in programs:
        machine = compile_dag(nodes, initial_registers=initial)
        def builder_edge(edge):
            kind, n = parse_edge(edge)
            if kind == "ENode":
                return n
            if kind == "EHalt":
                return "halt"
            if kind in ("EInc", "EDecnz"):
                return f"3.{REGISTERS[n]}.{'inc' if kind == 'EInc' else 'decnz'}"
            return f"_{'break' if kind == 'EBreak' else 'continue'}.{n}"
        builder = SimpleNamespace(sequences=[SimpleNamespace(
            seq=tuple(builder_edge(e) for e in nodes[q]), name=f"test{q}")
            for q in range(len(nodes))])
        if compile_builder(builder, initial_registers=initial).encoded() != machine.encoded():
            raise ValueError("builder adapter changed the generated table")
        builder_roundtrips += 1
        initial_configuration_check(machine)
        symbolic_cases += machine.check_sites()["cases_passed"]
        q, head, tape = 0, 0, {}
        for _ in range(100000):
            q, head = concrete_step(machine, q, tape, head)
            if q == machine.halt:
                break
        else:
            raise ValueError("small whole-machine regression failed to halt")
        checks += 1
    rejected = 0
    bad = [({0: ("ENode 0", "EHalt")}, {}),
           ({0: ("ENode 1", "EHalt")}, {}),
           ({0: ("EInc 9", "EHalt")}, {}),
           ({0: ("unknown", "EHalt")}, {}),
           ({0: ("EBreak 2", "EHalt")}, {}),
           ({0: ("EContinue 1", "EHalt")}, {}),
           ({0: ("EHalt", "EDecnz 0")}, {}),
           ({0: ("EHalt", "EHalt")}, {"gap": 6}),
           ({0: ("EHalt", "EHalt")}, {"dispatcher_threshold": 8}),
           ({0: ("EHalt", "EHalt")}, {"initial_registers": [-1] * 9}),
           (programs[-1][0], {"generic_decrement": False})]
    for nodes, kwargs in bad:
        try:
            compile_dag(nodes, **kwargs)
        except ValueError:
            rejected += 1
        else:
            raise ValueError("invalid input regression was accepted")
    # The long zero path requires a longer dispatcher; exercise that variant.
    nodes = {q: ("ENode " + str(q+1), "EHalt") for q in range(10)}
    nodes[10] = ("EInc 0", "EHalt")
    long_zero = compile_dag(nodes)
    symbolic_cases += long_zero.check_sites()["cases_passed"]
    initial_configuration_check(long_zero)
    long_zero_concrete = concrete_site_checks(long_zero, samples=4)["cases_passed"]
    if long_zero.evidence["dispatcher_threshold"] != 13:
        raise ValueError("long-zero dispatcher was not extended")
    native = compile_dag(programs[2][0], initial_registers=programs[2][1],
                         generic_decrement=False)
    symbolic_cases += native.check_sites()["cases_passed"]
    return {"small_blank_machine_halts_passed": checks,
            "builder_adapter_roundtrips_passed": builder_roundtrips,
            "invalid_inputs_rejected": rejected, "symbolic_cases_passed": symbolic_cases,
            "long_zero_dispatcher_checked": True, "patched_right_decrement_checked": True,
            "long_zero_concrete_instruction_cases_passed": long_zero_concrete,
            "native_zero_return_variant_checked": True,
            "formal_proof": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scratch", type=Path, required=True)
    parser.add_argument("--output-evidence", type=Path)
    parser.add_argument("--initializer", choices=("direct", "compact"), default="direct")
    args = parser.parse_args()
    scratch = args.scratch.resolve()
    if scratch == ROOT or ROOT in scratch.parents or scratch == Path("/"):
        parser.error("scratch must be outside the repository and not filesystem root")
    scratch.mkdir(parents=True, exist_ok=True)
    source = git_bytes(None, DAG_PATH)
    nodes, names = parse_dag(source.decode())
    results = []
    for initial, stem in (([0] * 9, "dag219-zero"), ([2] + [0] * 8, "dag219-nextproof2")):
        machine = compile_dag(nodes, names, initial_registers=initial,
                              initializer=args.initializer)
        machine.evidence["initializer_check"] = initial_configuration_check(machine)
        machine.check_sites()
        if not results:
            machine.evidence["concrete_box_checks"] = box_checks(machine)
            machine.evidence["concrete_instruction_checks"] = concrete_site_checks(machine)
        output = scratch / (stem + ".tm")
        machine.save(output)
        # Reparse every generated row independently of the label assembler.
        reparsed = {}
        for line in output.read_text().splitlines():
            if line.startswith("#"):
                continue
            q, b, w, direction, target = line.split()
            key = int(q), int(b)
            if key in reparsed:
                raise ValueError("duplicate emitted row")
            reparsed[key] = int(w), direction, int(target)
        if reparsed != machine.table:
            raise ValueError("saved table differs from the assembled table")
        machine.evidence["table_roundtrip_exact"] = True
        machine.evidence["table_filename"] = output.name
        results.append(machine.evidence)
    result = {"upstream_commit": COMMIT, "DAG_source": DAG_PATH,
              "DAG_source_sha256": hashlib.sha256(source).hexdigest(),
              "assembler": "mira_backend.py",
              "assembler_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "baseline_variants": results,
              "offline_regressions": offline_regressions(),
              "new_ZFC_machine_or_state_bound_claimed": False,
              "conclusion": "Fresh single-marker assembly works in executable checks; its initializer and decoder are fully charged, and no Lean simulation or consistency calibration is supplied."}
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output_evidence:
        args.output_evidence.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()

