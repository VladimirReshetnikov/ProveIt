#!/usr/bin/env python3
"""Reconstruct U211 from its frozen U212 parent and nine literal rotations."""
from pathlib import Path
import json
from core import census, encode, read_table, require, sha256, write_json

ROOT = Path(__file__).resolve().parents[1]
PARENT_SHA = "386ce16259d4c97e4af31b3ba494feaff11a0a1a066e0235dddc154b4cea38c4"
OLD_SOURCE_SHA = "7b6539dc67b66ff73f22554018d7af5985d85574460a73fea5f025103c523d00"
ROTATED_SHA = "e3fe20c1d0181997354d0cf97b8ccceb85a1ec8055ad32ea5d02cacdf1a1b9d5"
NATIVE_SHA = "7edae566b4c2e5c34d88030e0ae7caa49edda32c174b06b1a68bf9eb78567c8d"
SOURCE_SHA = "a1c81a3abff846a329a109927ce92d0be1553b7af2671855cdfe5bc4d6d953d1"


def new_address(word, roots, side):
    for prefix in roots:
        if not word.startswith(prefix):
            continue
        suffix = word[len(prefix):]
        if side == 0:
            if suffix.startswith("00"):
                return prefix + "0" + suffix[2:]
            if suffix.startswith("01"):
                return prefix + "10" + suffix[2:]
            require(suffix.startswith("1"), "Invalid left-rotation leaf")
            return prefix + "11" + suffix[1:]
        if suffix.startswith("0"):
            return prefix + "00" + suffix[1:]
        if suffix.startswith("10"):
            return prefix + "01" + suffix[2:]
        require(suffix.startswith("11"), "Invalid right-rotation leaf")
        return prefix + "1" + suffix[2:]
    return word


def build():
    raw = (ROOT / "inputs/u212.native.tm").read_bytes()
    source_raw = (ROOT / "inputs/u212.sites.json").read_bytes()
    require(sha256(raw) == PARENT_SHA, "Parent table identity")
    require(sha256(source_raw) == OLD_SOURCE_SHA, "Parent source identity")
    table = read_table(ROOT / "inputs/u212.native.tm")
    census(table, 212, 254)
    source = json.loads(source_raw)
    rotations = json.loads((ROOT / "inputs/rotations.json").read_text())
    paths = json.loads((ROOT / "inputs/rotation_paths.json").read_text())
    require(len(rotations) == len(paths) == 9, "Nine rotations required")
    for (outer, inner, side), roots in zip(rotations, paths):
        require(side in (0, 1), "Invalid side")
        require(all(table[q, b][:2] == (b, 1)
                    for q in (outer, inner) for b in (0, 1)),
                "Rotation changes a non-pure decoder")
        require(table[outer, side][2] == inner, "Incorrect inner edge")
        require({k for k, v in table.items() if v[2] == inner} == {(outer, side)},
                "Inner decoder has another entry")
        require(all(d == 1 for _, (w, d, z) in table.items()
                    if z in (outer, inner)), "Backward runtime reentry")
        if side == 0:
            a, b, c = table[inner, 0][2], table[inner, 1][2], table[outer, 1][2]
            table[outer, 0], table[outer, 1] = (0, 1, a), (1, 1, inner)
            table[inner, 0], table[inner, 1] = (0, 1, b), (1, 1, c)
        else:
            a, b, c = table[outer, 0][2], table[inner, 0][2], table[inner, 1][2]
            table[outer, 0], table[outer, 1] = (0, 1, inner), (1, 1, c)
            table[inner, 0], table[inner, 1] = (0, 1, a), (1, 1, b)
        source = [[new_address(p, roots, side), op, arg] for p, op, arg in source]
    census(table, 212, 254)
    rotated = encode(table)
    require(sha256(rotated) == ROTATED_SHA, "Rotated table identity")
    source_bytes = (json.dumps(source, separators=(",", ":")) + "\n").encode("ascii")
    require(sha256(source_bytes) == SOURCE_SHA, "Rotated source identity")

    # Replace the right-tagged state 181 by the left-tagged state 220.
    child = {(q, bit): (w, d, 220 if z == 181 else z)
             for (q, bit), (w, d, z) in table.items() if q != 181}
    child[220, 0] = (0, -1, 129)
    states = census(child, 211, 254)
    native = encode(child)
    require(sha256(native) == NATIVE_SHA, "Final native identity")
    rename = {q: i for i, q in enumerate(sorted(states))}
    rename[254] = 211
    dense = {(rename[q], bit): (w, d, rename[z])
             for (q, bit), (w, d, z) in child.items()}
    census(dense, 211, 211)
    inverse = {v: k for k, v in rename.items()}
    require({(inverse[q], bit): (w, d, inverse[z])
             for (q, bit), (w, d, z) in dense.items()} == child,
            "Dense renaming is not a table isomorphism")
    output = ROOT / "machine"
    output.mkdir(exist_ok=True)
    for name, data in [("rotated212.native.tm", rotated), ("u211.native.tm", native),
                       ("u211.tm", encode(dense)), ("sites.json", source_bytes)]:
        (output / name).write_bytes(data)
    write_json(output / "state_map.json", {"native_to_dense": rename,
               "dense_to_native": inverse, "native_halt": 254, "dense_halt": 211})
    result = {
        "status": "EXACT_CONSTRUCTION_PASS", "working_states": 211,
        "transition_rows": 422, "start": 0, "dense_halt": 211, "native_halt": 254,
        "symbols": [0, 1], "blank": 0, "tapes": 1, "tape_index": "integers",
        "initial_head": 0, "moves": ["L", "R"], "rotations": 9,
        "deleted_native_state": 181, "fold_keeper": 220, "fold_helper": 129,
        "all_working_states_graph_reachable": True,
        "parent_native_sha256": PARENT_SHA, "rotated_native_sha256": ROTATED_SHA,
        "native_sha256": NATIVE_SHA, "dense_sha256": sha256(encode(dense)),
        "source_sha256": SOURCE_SHA,
    }
    write_json(output / "summary.json", result)
    print(json.dumps(result, indent=2))
    return result


if __name__ == "__main__":
    build()
