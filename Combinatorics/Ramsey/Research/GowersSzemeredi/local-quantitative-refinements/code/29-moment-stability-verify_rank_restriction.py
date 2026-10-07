"""Exact finite checks for the all-tuples affine-rank restriction lemma.

This audits actual selections against independent linear-algebra rank counts.
It deliberately includes low-dimensional cases with no generic tuples, repeated
entries, nonlinear graph maps, and systems with more than one relation.
Only prime fields are used in this finite audit; the proof allows prime powers.
"""

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from pathlib import Path


def rref(rows, p):
    a = [[v % p for v in row] for row in rows]
    pivots = []
    if not a:
        return a, pivots
    r = 0
    for c in range(len(a[0])):
        hit = next((i for i in range(r, len(a)) if a[i][c]), None)
        if hit is None:
            continue
        a[r], a[hit] = a[hit], a[r]
        inv = pow(a[r][c], -1, p)
        a[r] = [(x * inv) % p for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][c]:
                f = a[i][c]
                a[i] = [(x - f * y) % p for x, y in zip(a[i], a[r])]
        pivots.append(c)
        r += 1
        if r == len(a):
            break
    return a[:r], pivots


def rank(columns, p):
    if not columns:
        return 0
    return len(rref(list(map(list, zip(*columns))), p)[1])


def solution_tuples(points, relations, p):
    rows, pivots = rref(relations, p)
    arity = len(relations[0])
    assert all(sum(row) % p == 0 for row in rows)
    free = [i for i in range(arity) if i not in pivots]
    point_set = set(points)
    dim = len(points[0])
    for values in product(points, repeat=len(free)):
        xs = [None] * arity
        for i, x in zip(free, values):
            xs[i] = x
        for row, i in zip(rows, pivots):
            xs[i] = tuple((-sum(row[j] * xs[j][h] for j in free)) % p
                          for h in range(dim))
        if all(x in point_set for x in xs):
            yield tuple(xs), tuple(xs[i] for i in free)


def respected(xs, phi, relations, p):
    codim = len(phi[xs[0]])
    return all(sum(row[i] * phi[xs[i]][j] for i in range(len(xs))) % p == 0
               for row in relations for j in range(codim))


def cube_relations(k, p):
    verts = list(product(range(2), repeat=k))
    zero = verts.index((0,) * k)
    unit = [verts.index(tuple(int(i == j) for i in range(k)))
            for j in range(k)]
    rows = []
    for idx, vertex in enumerate(verts):
        if sum(vertex) < 2:
            continue
        row = [0] * len(verts)
        row[idx] = 1
        row[zero] = sum(vertex) - 1
        for j in range(k):
            row[unit[j]] -= vertex[j]
        rows.append([v % p for v in row])
    return rows


def audit_case(name, p, points, phi, relations, t=1):
    _, pivots = rref(relations, p)
    s = len(relations[0]) - len(pivots)
    augdim = len(points[0]) + len(next(iter(phi.values()))) + 1
    lam = Fraction(1, p ** t)
    all_tuples = []
    profile = Counter()
    expected_x = Fraction(0)
    expected_y = Fraction(0)
    for xs, free in solution_tuples(points, relations, p):
        r = rank([x + (1,) for x in xs], p)
        assert r == rank([x + (1,) for x in free], p)
        g = rank([x + phi[x] + (1,) for x in xs], p)
        good = respected(xs, phi, relations, p)
        if good:
            assert g <= s
            expected_x += lam ** g
        else:
            assert g >= r + 1
            expected_y += lam ** g
        profile[(r, g-r, good)] += 1
        all_tuples.append((xs, good, g))

    # Enumerate actual random maps. Each independent output row is uniform.
    map_count = p ** (t * augdim)
    x_sum = 0
    y_sum = 0
    observed_survivals = Counter()
    forms = list(product(range(p), repeat=augdim))
    for matrix_rows in product(forms, repeat=t):
        selected = {x for x in points
                    if all(sum(a*z for a,z in zip(row, x+phi[x]+(1,))) % p == 0
                           for row in matrix_rows)}
        for xs, good, g in all_tuples:
            if all(x in selected for x in xs):
                observed_survivals[xs] += 1
                x_sum += int(good)
                y_sum += int(not good)
    assert Fraction(x_sum, map_count) == expected_x
    assert Fraction(y_sum, map_count) == expected_y
    for xs, _, g in all_tuples:
        assert Fraction(observed_survivals[xs], map_count) == lam ** g

    rank_poly = Fraction(0)
    deg_poly = Fraction(0)
    for free in product(points, repeat=s):
        r = rank([x + (1,) for x in free], p)
        rank_poly += lam ** r
        if r < s:
            deg_poly += lam ** r
    z = len(points) * lam
    prod_bound = z
    for i in range(s-1):
        prod_bound *= z + p ** i
    assert rank_poly <= prod_bound
    assert deg_poly <= prod_bound - z ** s
    assert expected_y <= lam * rank_poly
    good_count = sum(n for (r,e,g),n in profile.items() if g)
    assert expected_x >= lam ** s * good_count
    return {
        "name": name, "p": p, "points": len(points), "free_coordinates": s,
        "t": t, "maps_exhausted": map_count, "tuples": len(all_tuples),
        "generic_tuples": sum(n for (r,e,g),n in profile.items() if r == s),
        "respected_tuples": good_count,
        "expected_good": str(expected_x), "expected_bad": str(expected_y),
        "rank_polynomial": str(rank_poly), "rank_product_bound": str(prod_bound),
        "rank_profile": [dict(domain_rank=r, full_error_rank=e,
                              respected=g, count=n)
                         for (r,e,g),n in sorted(profile.items())],
    }


def main(output_path):
    cases = []
    pts2 = list(product(range(2), repeat=2))
    phi2 = {x: (x[0]*x[1] % 2,) for x in pts2}
    cases.append(audit_case("binary quadratic, additive quadruples", 2,
                            pts2, phi2, [[1,1,-1,-1]], t=2))
    cases.append(audit_case("binary quadratic, all cube tuples nongeneric", 2,
                            pts2, phi2, cube_relations(3,2)))
    pts3 = [(x,) for x in range(3)]
    phi3 = {x: (x[0]**2 % 3,) for x in pts3}
    cases.append(audit_case("ternary quadratic, six-term tuples nongeneric", 3,
                            pts3, phi3, [[1,1,1,-1,-1,-1]]))
    pts4 = list(product(range(2), repeat=3))
    phi4 = {x: ((x[0]*x[1]) % 2, (x[1]*x[2]) % 2) for x in pts4}
    cases.append(audit_case("binary vector codomain, two balanced relations", 2,
                            pts4, phi4, [[1,1,-1,-1,0,0],
                                         [0,0,1,1,-1,-1]]))
    subset = pts4[:5]
    cases.append(audit_case("non-subspace domain with repeated entries", 2,
                            subset, phi4, [[1,1,-1,-1]]))
    payload = {
        "arithmetic": "exact integers and fractions",
        "assertions_passed": True,
        "scope": "exhaustive tuples and random maps for listed finite cases only",
        "cases": cases,
    }
    out = Path(output_path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({"assertions_passed": True, "cases": len(cases),
                      "map_tuple_checks": sum(x["maps_exhausted"]*x["tuples"]
                                              for x in cases),
                      "output": str(out)}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().with_name("rank_restriction_checks.json"),
        help="output JSON path; defaults to rank_restriction_checks.json beside this script",
    )
    main(parser.parse_args().output)
