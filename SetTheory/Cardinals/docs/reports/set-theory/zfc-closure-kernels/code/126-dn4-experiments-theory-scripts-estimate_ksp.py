#!/usr/bin/env python3
"""Price a literal K/S/Peirce replacement using the old closed macro library.

The changed command omits rho8's read of u.  The first three AX arguments
and all other rows remain.  This is a source-size experiment; any literal
machine needs a recompiled decoder and its own runtime certificate.
"""
from functools import cache
from collections import defaultdict
import itertools
import json
import argparse
import flatten_macros as f
from logical_row_permutations import intervals

b = f.b
e = f.m.e


def get(n, path):
    for bit in path:
        n = n[int(bit)]
    return n


def set_at(n, path, value):
    if not path:
        return value
    side = int(path[0])
    children = list(n)
    children[side] = set_at(children[side], path[1:], value)
    return tuple(children)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--parameter-permutations", action="store_true")
    parser.add_argument("--basis", choices=("original", "dn4", "both"), default="both")
    args = parser.parse_args()
    out = e.OUTPUT_ROOT / "ksp_estimate"
    out.mkdir(parents=True, exist_ok=True)
    named = {name: n for n, name in f.macros.items() if name in ("a", "b", "c", "im")}
    for label, source in [
        ("original", e.BASELINE_SOURCE),
        ("dn4", e.DN4_SOURCE),
    ]:
        if args.basis not in ("both", label):
            continue
        root = b.tree(json.loads(source.read_text()))
        rows, graph, initial = b.graph(b.sites(root))
        first, end = intervals(rows, graph)[8]
        first_path, last_path = rows[first][0], rows[end - 1][0]
        prefix = ""
        for a, c in zip(first_path, last_path):
            if a != c:
                break
            prefix += a
        region = get(root, prefix)
        indices = {path: i for i, (path, _, _) in enumerate(rows)}
        before, after = [], []
        def partition(n, path):
            ss = b.sites(n, path)
            low, high = indices[ss[0][0]], indices[ss[-1][0]]
            if high < first:
                before.append(n)
            elif low >= end:
                after.append(n)
            elif first <= low and high < end:
                return
            else:
                partition(n[0], path + "0"); partition(n[1], path + "1")
        partition(region, prefix)
        assert all(b.boundary(n) == (0, 0, False) for n in before + after)
        atoms = dict(named)
        head = []
        for i, n in enumerate(before):
            name = "before" + str(i)
            atoms[name] = n
            head.append(name)
        tail = []
        for i, n in enumerate(after):
            name = "after" + str(i)
            atoms[name] = n
            tail.append(name)
        atom_name = {n: name for name, n in atoms.items()}
        old_nodes = set()
        def collect(n):
            if n in old_nodes:
                return
            old_nodes.add(n)
            if not b.is_leaf(n):
                collect(n[0]); collect(n[1])
        collect(root)
        @cache
        def flatten(n):
            if n in atom_name:
                return (atom_name[n],)
            if b.is_leaf(n):
                return None
            left, right = flatten(n[0]), flatten(n[1])
            return left + right if left is not None and right is not None else None
        library = defaultdict(list)
        for n in old_nodes:
            word = flatten(n)
            if word and b.boundary(n) == (0, 0, False):
                library[word].append(n)
        @cache
        def admissible(n, zeros):
            ss = b.sites(n)
            leading = len(ss[0][0]) - len(ss[0][0].lstrip("0"))
            return b.metrics(n)["maximum_zero_run"] <= 6 and zeros + leading <= 6
        words = {
            "K": "a b a im im".split(),
            "S": "a b c im im a b im a c im im im".split(),
            "P": "a b im a im a im".split(),
        }
        choices = ["".join(p) for p in itertools.permutations("abc")] if args.parameter_permutations else ["abc"]
        best_count = 10**9
        for order, parameters in itertools.product(itertools.permutations("KSP"), itertools.product(choices, repeat=3)):
            selected_words = {}
            for name, parameters_for_row in zip("KSP", parameters):
                renaming = dict(zip("abc", parameters_for_row))
                selected_words[name] = [renaming.get(t, t) for t in words[name]]
            word = tuple(head + sum([selected_words[name] for name in order], []) + tail)
            @cache
            def solve(i, j, zeros):
                if zeros > 6:
                    return None
                candidates = []
                for n in library.get(word[i:j], []):
                    if admissible(n, zeros):
                        candidates.append((0, b.metrics(n)["maximum_depth"], n))
                if i + 1 < j:
                    for k in range(i + 1, j):
                        left, right = solve(i, k, zeros + 1), solve(k, j, 0)
                        if left is not None and right is not None:
                            candidates.append((left[0] + right[0] + 1, 1 + max(left[1], right[1]), (left[2], right[2])))
                return min(candidates, key=lambda v: (v[0], v[1])) if candidates else None
            answer = solve(0, len(word), len(prefix) - len(prefix.rstrip("0")))
            if answer is None:
                print(label, order, "NO ADMISSIBLE TREE")
                continue
            new = set_at(root, prefix, answer[2])
            b.graph(b.sites(new))
            stats = b.metrics(new)
            tag = label + "_" + "".join(order) + ("_" + "_".join(parameters) if args.parameter_permutations else "")
            if args.parameter_permutations and stats["dag_nodes"] >= best_count:
                continue
            best_count = stats["dag_nodes"]
            print(tag, "added-occurrence-cost", answer[0], "macro-word", len(word), stats, flush=True)
            (out / ("sites_" + tag + ".json")).write_bytes(b.json_bytes(b.sites(new), compact=True))
            (out / ("recipe_" + tag + ".json")).write_bytes(b.json_bytes({
                "basis": label,
                "old_rho8_leaf_interval": [first, end],
                "region_prefix": prefix,
                "preserved_before_chunks": [len(b.sites(n)) for n in before],
                "preserved_after_chunks": [len(b.sites(n)) for n in after],
                "new_axiom_order": order,
                "new_axiom_postfix": selected_words,
                "new_axiom_parameter_order": dict(zip("KSP", parameters)),
                "macro_word": word,
                "new_compound_occurrence_cost": answer[0],
                "source_metrics": stats,
                "scope": "Source grammar cost only; no TM-state bound and no runtime correctness claim.",
            }))


if __name__ == "__main__":
    main()
