#!/usr/bin/env python3
"""Independent exact local certificate for Plain U209 -> U208.

This program imports no candidate-discovery or supplied verification module.
Guard checking enumerates complete *last-step histories*, not bounded blank runs.
Each path begins with arbitrary tape on all touched cells and arbitrary exterior.
"""
from pathlib import Path
import hashlib
import itertools
import json
import argparse

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "inputs"
CAND = ROOT / "machine"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        q, b, w, d, r = line.split()
        q, b, w, r = map(int, (q, b, w, r))
        require((q, b) not in table, "Duplicate row")
        require(b in (0, 1) and w in (0, 1) and d in ("L", "R"), "Bad alphabet")
        table[q, b] = (w, 1 if d == "R" else -1, r)
    return table


def census(table, expected, halt):
    states = {q for q, b in table}
    require(len(states) == expected, "Wrong state count")
    require(set(table) == {(q, b) for q in states for b in (0, 1)}, "Incomplete table")
    require({r for w, d, r in table.values()} - states == {halt}, "Invalid halt")
    seen = {0}
    queue = [0]
    for q in queue:
        for b in (0, 1):
            r = table[q, b][2]
            if r not in seen and r != halt:
                seen.add(r)
                queue.append(r)
    require(seen == states, "Unreachable working state")
    return states


def predecessor_histories(table, q, depth):
    incoming = {}
    for (p, b), (w, d, r) in table.items():
        incoming.setdefault(r, []).append((p, b, w, d, r))
    def walk(state, remaining):
        if remaining == 0 or state == 0:
            return [[]]
        return [path + [row] for row in incoming.get(state, [])
                for path in walk(row[0], remaining - 1)]
    return walk(q, depth)


def check_guard(table, state, depth, condition, conclusion):
    paths = predecessor_histories(table, state, depth)
    require(paths, "Empty incoming proof")
    records = []
    for path in paths:
        start = -sum(row[3] for row in path)
        pos = start
        touched = set(condition) | set(conclusion)
        for row in path:
            touched.add(pos)
            pos += row[3]
        require(pos == 0, "Bad relative history")
        positions = sorted(touched)
        consistent = 0
        satisfies_condition = 0
        for bits in itertools.product((0, 1), repeat=len(positions)):
            tape = dict(zip(positions, bits))
            pos = start
            viable = True
            for p, b, w, d, r in path:
                if tape[pos] != b:
                    viable = False
                    break
                tape[pos] = w
                pos += d
            if not viable:
                continue
            consistent += 1
            if not all(tape[i] == b for i, b in condition.items()):
                continue
            satisfies_condition += 1
            require(all(tape[i] == b for i, b in conclusion.items()),
                    ("Guard counterexample", state, path, tape))
        records.append({"rows": path, "start_head": start, "touched_positions": positions,
                        "viable_assignments": consistent,
                        "assignments_satisfying_condition": satisfies_condition})
    return {"state": state, "depth": depth, "condition": condition,
            "conclusion": conclusion, "histories": records,
            "scope": "Exhaustive suffix histories from arbitrary tape; exterior never read."}


def step(table, q, head, tape):
    require(head in tape, "Read of opaque exterior")
    w, d, r = table[q, tape[head]]
    tape[head] = w
    return r, head + d


def check_case(old, new, q, bits, count):
    rho = lambda x: 172 if x == 211 else x
    before = dict(bits)
    old_tape = before.copy()
    old_q, old_head = step(old, q, 0, old_tape)
    new_tape = before.copy()
    new_q, new_head = rho(q), 0
    path = [(new_q, new_head)]
    for i in range(count):
        require(new_q != 254, "Internal halt")
        new_q, new_head = step(new, new_q, new_head, new_tape)
        path.append((new_q, new_head))
    require((new_q, new_head, new_tape) == (rho(old_q), old_head, old_tape),
            ("Macro mismatch", q, bits, path))
    return {"old_state": q, "known_bits": bits, "old_steps": 1,
            "new_steps": count, "new_state_head_path": path,
            "unread_exterior_arbitrary": True}


def main():
    old = read(BASE / "u209.native.tm")
    new = read(CAND / "u208.native.tm")
    old_states = census(old, 209, 254)
    new_states = census(new, 208, 254)
    require(new_states == old_states - {211}, "Wrong deleted state")
    rho = lambda q: 172 if q == 211 else q
    expected = {(q, b): (w, d, rho(r)) for (q, b), (w, d, r) in old.items() if q != 211}
    expected[172, 0] = (0, -1, 214)
    require(expected == new, "Patch differs from specified quotient")
    require(hashlib.sha256((BASE / "u209.native.tm").read_bytes()).hexdigest() ==
            "891455876f2684b2bd2a9118092715590028fbdb227aa7055030536714d8b7a4",
            "Copied parent differs")
    require((CAND / "sites.json").read_bytes() == (BASE / "u209.sites.json").read_bytes(),
            "Source changed")
    mapping = json.loads((CAND / "state_map.json").read_text())
    renaming = {int(k): v for k, v in mapping["native_to_dense"].items()}
    require(set(renaming) == new_states | {254}, "Relabeling domain")
    require(set(renaming.values()) == set(range(209)), "Relabeling bijection")
    require(renaming[0] == 0 and renaming[254] == 208, "Relabeling endpoints")
    dense = read(CAND / "u208.tm")
    require({(renaming[q], b): (w, d, renaming[r]) for (q, b), (w, d, r) in new.items()} == dense,
            "Dense relabeling mismatch")
    census(dense, 208, 208)
    guards = [
        check_guard(old, 172, 2, {}, {-2: 1, -1: 0}),
        check_guard(old, 211, 3, {0: 0}, {-1: 1}),
    ]
    cases = [
        check_case(old, new, 172, {-2: 1, -1: 0, 0: 0}, 7),
        check_case(old, new, 211, {-1: 1, 0: 0}, 3),
        check_case(old, new, 172, {0: 1}, 1),
        check_case(old, new, 211, {0: 1}, 1),
    ]
    ordinary = [(q, b) for q, b in old if q not in {172, 211}]
    for q, b in ordinary:
        w, d, r = old[q, b]
        require(new[rho(q), b] == (w, d, rho(r)), "Ordinary row fails")
    result = {
        "status": "INDEPENDENT_U208_ALL_TAPE_LOCAL_AUDIT_PASS",
        "parent_states": 209, "candidate_states": 208, "candidate_rows": 416,
        "graph_reachable_states": 208,
        "ordinary_rows": len(ordinary), "macro_cases": cases, "guard_proofs": guards,
        "time_formula": "T_new = T_old + 6*N(172,0) + 2*N(211,0)",
        "time_bounds": "T_old <= T_new <= 7*T_old",
        "theorem_scope": "Every common arbitrary binary tape from state 0, same head coordinate",
        "no_source_or_numerical_calculus_assumption_used_in_local_proof": True,
        "sha256": {name: hashlib.sha256(((BASE if name=="u209.native.tm" else CAND) / name).read_bytes()).hexdigest()
                   for name in ("u209.native.tm", "u208.native.tm", "u208.tm", "sites.json")},
        "proof_boundary": "Finite executable certificate plus mathematical suffix and run induction; not a kernel theorem.",
    }
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "build/independent_local.json")
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
