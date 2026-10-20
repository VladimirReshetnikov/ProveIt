#!/usr/bin/env python3
"""Emit command-selector permutations, preserving AX selectors 3+c."""
from pathlib import Path
import itertools
import json
import sys

import explore_source as e

b = e.b
PATHS = ["1111", "1110101", "1110100101"]
NAMES = ["MP", "DROP", "NIP"]


def at(n, path):
    for bit in path:
        n = n[int(bit)]
    return n


def replace(n, replacements, path=""):
    if path in replacements:
        return replacements[path]
    return n if b.is_leaf(n) else tuple(replace(n[i], replacements, path + str(i)) for i in (0, 1))


def main():
    out = e.OUTPUT_ROOT / "selector_permutations"
    out.mkdir(parents=True, exist_ok=True)
    for label, source in [
        ("original", e.BASELINE_SOURCE),
        ("dn4", e.DN4_SOURCE),
    ]:
        root = b.tree(json.loads(source.read_text()))
        bodies = [at(root, path) for path in PATHS]
        assert [b.boundary(n) for n in bodies] == [(0, 0, False), (0, 0, False), (0, 0, True)]
        for permutation in itertools.permutations(range(3)):
            new = replace(root, {path: bodies[permutation[i]] for i, path in enumerate(PATHS)})
            index = "".join(map(str, permutation))
            try:
                b.graph(b.sites(new))
            except Exception as error:
                print(label, index, "bad graph", str(error))
                continue
            stats = b.metrics(new)
            recipe = {
                "basis": label,
                "selector_to_old_selector": list(permutation),
                "selector_to_command": [NAMES[i] for i in permutation],
                "body_paths": PATHS,
                "body_boundaries": [b.boundary(n) for n in bodies],
                "source_metrics": stats,
                "proof": "Command encodings are permuted by a bijection on selectors 0,1,2; AX selector 3+c and every command operand are unchanged.",
            }
            (out / f"sites_{label}_{index}.json").write_bytes(b.json_bytes(b.sites(new), compact=True))
            (out / f"recipe_{label}_{index}.json").write_bytes(b.json_bytes(recipe))
            print(label, index, stats)


if __name__ == "__main__":
    main()
