#!/usr/bin/env python3
"""Source-cost probe for Source 116's canonical equality vacuity family."""
from functools import cache
from collections import defaultdict
import json
import flatten_macros as f

b = f.b
e = f.m.e
PREFIX = "1110100100111011110"


def at(n, path):
    for bit in path:
        n = n[int(bit)]
    return n


def replace(n, path, value):
    if not path:
        return value
    z = list(n)
    z[int(path[0])] = replace(z[int(path[0])], path[1:], value)
    return tuple(z)


def main():
    root = b.tree(json.loads(e.DN4_SOURCE.read_text()))
    atoms = {name: n for n, name in f.macros.items() if name in ("a", "b", "c", "all", "im", "neg", "ac_s1s2")}
    atoms["inc1"] = ("CI", 1)
    names = {n: name for name, n in atoms.items()}
    @cache
    def flat(n):
        if n in names:
            return (names[n],)
        if b.is_leaf(n):
            return None
        x, y = flat(n[0]), flat(n[1])
        return x + y if x is not None and y is not None else None
    original_word = flat(at(root, PREFIX))
    assert original_word == tuple("c a b all inc1 all im neg im im neg ac_s1s2".split())
    word = tuple("a b all inc1".split()) + original_word[1:]
    old = set()
    def collect(n):
        if n in old:
            return
        old.add(n)
        if not b.is_leaf(n):
            collect(n[0]); collect(n[1])
    collect(root)
    library = defaultdict(list)
    for n in old:
        s = flat(n)
        if s and b.boundary(n) == (0, 0, False):
            library[s].append(n)
    @cache
    def valid(n, zeros):
        leading_path = b.sites(n)[0][0]
        leading = len(leading_path) - len(leading_path.lstrip("0"))
        return b.metrics(n)["maximum_zero_run"] <= 6 and zeros + leading <= 6
    @cache
    def solve(i, j, zeros):
        if zeros > 6:
            return None
        options = []
        for n in library.get(word[i:j], []):
            if valid(n, zeros):
                options.append((0, b.metrics(n)["maximum_depth"], n))
        for k in range(i + 1, j):
            left, right = solve(i, k, zeros + 1), solve(k, j, 0)
            if left is not None and right is not None:
                options.append((left[0] + right[0] + 1, 1 + max(left[1], right[1]), (left[2], right[2])))
        return min(options, key=lambda x: (x[0], x[1])) if options else None
    result = solve(0, len(word), len(PREFIX) - len(PREFIX.rstrip("0")))
    assert result is not None
    new = replace(root, PREFIX, result[2])
    stats = b.metrics(new)
    assert stats["maximum_zero_run"] <= 6
    b.graph(b.sites(new))
    out = e.OUTPUT_ROOT / "canonical_ve"
    out.mkdir(parents=True, exist_ok=True)
    (out / "sites_dn4_canonical_ve_reparsed.json").write_bytes(b.json_bytes(b.sites(new), compact=True))
    (out / "recipe_dn4_canonical_ve_reparsed.json").write_bytes(b.json_bytes({"prefix": PREFIX, "old_word": original_word, "new_word": word, "new_compound_occurrence_cost": result[0], "metrics": stats, "scope": "Source cost only; exact Source116/K230 theory adapter and runtime are separate."}))
    print(stats, "new compound occurrence cost", result[0])


if __name__ == "__main__":
    main()
