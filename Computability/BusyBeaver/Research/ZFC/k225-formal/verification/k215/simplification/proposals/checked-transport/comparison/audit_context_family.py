#!/usr/bin/env python3
"""Independent finite all-tape premises for every subset of context215 patches.

The finite certificate is not a proof-assistant endpoint. The accompanying
mathematical theorem explains why its checks imply all-tape halting transport.
No upstream executable is imported or run. Standard library only.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

PATCHES = [
    ((13, 1), (1, -1, 81)),
    ((27, 1), (0, -1, 302)),
    ((83, 1), (0, -1, 57)),
    ((156, 1), (1, 1, 52)),
    ((198, 0), (1, -1, 54)),
]
BLOCKS = [
    ((13, 1), {-2: 1, -1: 0, 0: 1}, 2, 4),
    ((13, 1), {-1: 1, 0: 1}, 3, 3),
    ((27, 1), {-1: 0, 0: 1}, 2, 2),
    ((83, 1), {-1: 1, 0: 1}, 2, 2),
    ((156, 1), {0: 1, 1: 1}, 2, 2),
    ((198, 0), {-1: 1, 0: 0}, 2, 2),
]
PINS = {
    "old": "9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2",
    "new": "da20914ad9bda3f75de0381f2c05a7b5e67d26199b57b870a5ea3b72511ab627",
}


def require(x, msg):
    if not x:
        raise ValueError(msg)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def table(path):
    rows = {}
    start = None
    for line in path.read_text().splitlines():
        line = line.strip()
        if line.startswith("#! start "):
            require(start is None, "duplicate start")
            start = int(line.split()[-1])
        if not line or line.startswith("#"):
            continue
        a = line.split()
        require(len(a) == 5, "bad row arity")
        q, r, w, d, z = a
        q, r, w, z = map(int, (q, r, w, z))
        require(d in ("L", "R") and r in (0, 1) and w in (0, 1), "bad action")
        require((q, r) not in rows, "duplicate row")
        rows[q, r] = w, 1 if d == "R" else -1, z
    require(start is not None, "no declared start")
    states = {q for q, _ in rows}
    require(set(rows) == {(q, b) for q in states for b in (0, 1)}, "incomplete working table")
    halts = {a[2] for a in rows.values()} - states
    require(len(halts) == 1, "wrong number of terminals")
    return rows, start, halts.pop()


def canonical(rows, start, halt, reflection=False):
    naming = {start: 0}
    visit = [start]
    for q in visit:
        for b in (0, 1):
            z = rows[q, b][2]
            if z != halt and z not in naming:
                naming[z] = len(naming)
                visit.append(z)
    require(set(naming) == {q for q, _ in rows}, "unreachable working state")
    naming[halt] = len(naming)
    return tuple((w, -d if reflection else d, naming[z])
                 for q in visit for b in (0, 1) for w, d, z in [rows[q, b]])


def execute_window(rows, q, context, steps, changed):
    cells, head = dict(context), 0
    trace = []
    for i in range(steps):
        require(head in cells, "read outside prescribed window")
        b = cells[head]
        require((q, b) in rows, "early terminal")
        require(i == 0 or (q, b) not in changed, "patch inside strict block interior")
        w, d, z = rows[q, b]
        trace.append([q, head, b, w, d, z])
        cells[head], head, q = w, head + d, z
    return (q, head, cells), trace


def histories(rows, q, depth):
    paths = [[]]
    target = q
    # Enumerate backward paths, retaining full row identities.
    paths = [(q, [])]
    for _ in range(depth):
        paths = [(p, [(p, b, w, d, z)] + suffix)
                 for target, suffix in paths
                 for (p, b), (w, d, z) in rows.items() if z == target]
    output = []
    for _, path in paths:
        head, writes = 0, {}
        # Ignore read feasibility: this is an overapproximation of histories.
        for p, b, w, d, z in path:
            writes[head] = w
            head += d
        output.append({"path": [list(row) for row in path],
                       "known": {pos-head: bit for pos, bit in writes.items()}})
    return output


def validate(old_path, new_path):
    require(sha(old_path) == PINS["old"] and sha(new_path) == PINS["new"], "input pin mismatch")
    old, start, halt = table(old_path)
    new, ns, nh = table(new_path)
    require((start, halt) == (ns, nh) == (0, 254), "start/halt mismatch")
    require(len(old) == len(new) == 430 and old.keys() == new.keys(), "table domain mismatch")
    delta = {row: new[row] for row in old if old[row] != new[row]}
    require(delta == dict(PATCHES), "different five-row patch")
    changed = set(delta)
    blocks = []
    for row, guard, a, b in BLOCKS:
        x, xt = execute_window(old, row[0], guard, a, changed)
        y, yt = execute_window(new, row[0], guard, b, changed)
        require(x == y, "unequal whole-window endpoint")
        blocks.append({"entry": list(row), "guard": guard, "old_steps": a,
                       "new_steps": b, "old_trace": xt, "new_trace": yt,
                       "endpoint": x})
    guards = []
    compatible_count = 0
    for q, bit in changed:
        depth = 2 if q == 13 else 1
        early = {start}
        for _ in range(depth):
            require(q not in early, "patch reachable before required history")
            early = {old[p, b][2] for p in early if p != halt for b in (0, 1)}
        hs = histories(old, q, depth)
        require(hs, "missing incoming history")
        for h in hs:
            known = h["known"]
            feasible = 0 not in known or known[0] == bit
            h["compatible_with_entry_read"] = feasible
            if feasible:
                compatible_count += 1
                known = {**known, 0: bit}
                choices = [i for i, (entry, guard, a, b) in enumerate(BLOCKS)
                           if entry == (q, bit) and all(known.get(k) == v for k, v in guard.items())]
                require(choices, "incoming history does not imply a block guard")
                h["block"] = choices[0]
        guards.append({"entry": [q, bit], "history_depth": depth, "histories": hs})
    family = []
    roots = []
    for bits in itertools.product((0, 1), repeat=len(PATCHES)):
        variant = dict(old)
        for flag, (row, action) in zip(bits, PATCHES):
            if flag:
                variant[row] = action
        for row, guard, a, b in BLOCKS:
            selected = bool(bits[next(i for i, (key, _) in enumerate(PATCHES) if key == row)])
            if selected:
                x, _ = execute_window(old, row[0], guard, a, changed)
                y, _ = execute_window(variant, row[0], guard, b, changed)
                require(x == y, "subset invalidates selected block")
        root = canonical(variant, start, halt)
        roots.append(root)
        family.append({"mask": ''.join(map(str, bits)), "selected_rows": [list(row) for flag, (row, _) in zip(bits, PATCHES) if flag],
                       "working_states": len(variant)//2, "graph_reachable_states": len(root)//2,
                       "rooted_graph_sha256": hashlib.sha256(repr(root).encode()).hexdigest(),
                       "synchronization_duration_preserving": not bool(bits[0])})
    require(len(set(roots)) == 32, "some subsets are state-renamings")
    # Each reflection reverses both moves at the root, immediately distinguishing it.
    require(not(set(roots) & {tuple((w, -d, z) for w, d, z in r) for r in roots}), "reflected duplicate")
    return {"status": "PASS", "pins": PINS, "changed_rows": [list(row) for row, _ in PATCHES],
            "blocks": blocks, "guard_histories": guards,
            "old_history_paths": sum(len(x['histories']) for x in guards),
            "compatible_old_history_paths": compatible_count,
            "literal_block_transitions": sum(x['old_steps']+x['new_steps'] for x in blocks),
            "family": family, "distinct_rooted_graphs": len(set(roots)),
            "scope": "Independent finite premises of an ordinary all-tape transport theorem; no compiled ZFC endpoint is claimed by this script.",
            "time_corollary": "At every synchronized endpoint T_new = T_old + 2*delayed_blocks; at halt T_old <= T_new <= 2*T_old. If the state-13 patch is omitted, synchronized times agree."}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--old', required=True, type=Path)
    p.add_argument('--new', required=True, type=Path)
    p.add_argument('--output', required=True, type=Path)
    a = p.parse_args()
    result = validate(a.old, a.new)
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status','old_history_paths','compatible_old_history_paths','literal_block_transitions','distinct_rooted_graphs')}, indent=2))


if __name__ == '__main__':
    main()
