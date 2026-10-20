#!/usr/bin/env python3
"""Reindex each retained logical axiom's object/formula parameters.

This does not delete or weaken a logical row.  Each row has all-numeric
parameters, so any permutation of a,b,c has the identical instance set.
u in the four-argument Lukasiewicz row is left unchanged.
"""
from functools import cache
import itertools
import json
import explore_source as e

b = e.b
STARTS = [
    (8, "111010010011001000"),
    (7, "11101001001101111100"),
    (6, "1110100100111000101"),
    (5, "111010010011100100100"),
    (4, "111010010011100101101"),
    (3, "1110100100111001110100111000"),
    (2, "11101001001110011101101"),
    (1, "1110100100111001111011101"),
    (0, "111010010011100111111"),
]
VARIABLES = {"a": 4, "b": 5, "c": 3}


def intervals(rows, graph):
    starts = [(which, next(i for i, (path, _, _) in enumerate(rows) if path.startswith(prefix))) for which, prefix in STARTS]
    result = {}
    for (which, first), (_, end) in zip(starts, starts[1:]):
        for i in range(first, end):
            step = graph[i]
            targets = step[2:] if step[0] in ("INC", "DEC") else step[1:] if step[0] == "JUMP" else ()
            assert all(first <= target <= end for target in targets), (which, i, step, first, end)
        result[which] = first, end
    return result


def transform(rows, regions, selections):
    row_choices = [(regions[which], {VARIABLES[old]: VARIABLES[new] for old, new in zip("abc", perm)}) for which, perm in selections.items()]
    out = []
    for i, (path, op, arg) in enumerate(rows):
        for (first, end), rename in row_choices:
            if first <= i < end and op in ("CI", "CD"):
                arg = rename.get(arg, arg)
        out.append((path, op, arg))
    return out


def main():
    out = e.OUTPUT_ROOT / "logical_row_permutations"
    out.mkdir(parents=True, exist_ok=True)
    results = []
    for label, source in [
        ("original", e.BASELINE_SOURCE),
        ("dn4", e.DN4_SOURCE),
    ]:
        original = json.loads(source.read_text())
        ordered, graph, initial = b.graph(original)
        regions = intervals(ordered, graph)
        allresults = []
        for which in range(1, 9):
            for perm in itertools.permutations("abc"):
                perm = "".join(perm)
                if perm == "abc":
                    continue
                word = transform(ordered, regions, {which: perm})
                new = b.tree(word)
                stats = b.metrics(new)
                tag = f"{label}_r{which}_{perm}"
                allresults.append((stats["dag_nodes"], which, perm, stats, tag, word))
        allresults.sort(key=lambda r: (r[0], r[1], r[2]))
        for dag_nodes, which, perm, stats, tag, word in allresults:
            print(tag, stats)
            (out / f"sites_{tag}.json").write_bytes(b.json_bytes(word, compact=True))
            (out / f"recipe_{tag}.json").write_bytes(b.json_bytes({
                "basis": label,
                "row_parameter_permutations": {which: perm},
                "leaf_intervals": {which: regions[which]},
                "source_metrics": stats,
                "scope": "Same logical-row instance set by a bijection on its numeric parameters; source operands change, not control successors.",
            }))
        results += [{"tag": tag, "dag_nodes": count, "row": which, "permutation": perm} for count, which, perm, _, tag, _ in allresults]
    (out / "summary.json").write_bytes(b.json_bytes(results))


if __name__ == "__main__":
    main()
