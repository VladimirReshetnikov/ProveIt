#!/usr/bin/env python3
"""Exact antipodal word enumeration for a rationally unfoldable example."""
from fractions import Fraction as Q
from itertools import product
import json
from fixed_exact import add, base, dot, fixed_max, gram_matrix, legal, mul, norm2, sub, unfold


def routes(g, axis):
    """Unfold all simple words from (axis,0) to (axis,1)."""
    first = (axis, 0)
    def visit(path, org, vec, seams):
        last = path[-1]
        if last == (axis, 1):
            yield (path, org, vec, seams)
            return
        for j, bit in product(range(3), (0, 1)):
            if j == last[0] or (j, bit) in path:
                continue
            no, nv, gate = unfold(g, *last, org, vec, j, bit)
            yield from visit(path+[(j, bit)], no, nv, seams+[gate])
    return list(visit([first], (Q(0), Q(0)), base(g, axis), []))


def position(org, vec, p):
    for j in vec:
        org = add(org, mul(p[j], vec[j]))
    return org


def scores(g, axis, p):
    start = position((Q(0), Q(0)), base(g, axis), p)
    q = tuple(1-x for x in p)
    out = []
    for path, org, vec, seams in routes(g, axis):
        end = position(org, vec, q)
        if legal(start, end, seams):
            out.append((norm2(sub(end,start)), path))
    return sorted(out)


def skew_test():
    g = gram_matrix(("1","1","4","0","80/401","0"))
    p = (Q(1,2), Q(1,2), Q(0))
    rows = scores(g, 2, p)
    corners = {str(v) : fixed_max(g, v)["squared_eccentricity"]
               for v in product((0,1), repeat=3)}
    assert all(Q(e) < rows[0][0] for e in corners.values())
    return {
        "gram": [[str(x) for x in row] for row in g],
        "p": list(map(str,p)), "q": [str(1-x) for x in p],
        "simple_words": len(routes(g, 2)), "admissible_words": len(rows),
        "squared_distance": str(rows[0][0]),
        "shortest_words_axis_then_bit": [w for val,w in rows if val==rows[0][0]],
        "squared_eccentricities_for_comparison": corners,
        "strict_conclusion":"Free diameter strictly exceeds the eccentricity of every vertex.",
        "status":"The tested pair supplies a lower bound for the diameter."}


if __name__ == "__main__":
    print(json.dumps(skew_test(), indent=2))
