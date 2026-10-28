#!/usr/bin/env python3
"""Recheck the two fixed downstream support bounds used by the recurrence."""
from fractions import Fraction
from itertools import combinations, permutations, product
import json
from certify import plan_data, dot, require


def small_supports(r, plan):
    _, _, operations = plan_data(r, plan)
    edges = list(combinations(range(r), 2))
    triples = sorted(set(permutations((2, 5, 5))))
    vectors = []
    for parts in operations:
        where = {v: j for j, part in enumerate(parts) for v in part}
        for triple in triples:
            weights = dict(zip(((0, 1), (0, 2), (1, 2)), triple))
            vectors.append(tuple(0 if where[a] == where[b] else
                                 weights[tuple(sorted((where[a], where[b])))]
                                 for a, b in edges))
    return vectors


def main():
    plans13 = [[[0,1,2,3,4],[5,6,7,8],[9,10,11,12]],
               [[12,10,1,6,4],[9,0,3,8],[5,2,7,11]],
               [[0,8,11,12,1],[7,10,4,3],[5,2,6,9]]]
    menus = [small_supports(13, p) for p in plans13]
    require([len(m) for m in menus] == [33]*3, "thirteen-group support lengths")
    norms = [[dot(v,v) for v in m] for m in menus]
    ab = [[dot(v,w) for w in menus[1]] for v in menus[0]]
    ac = [[dot(v,w) for w in menus[2]] for v in menus[0]]
    bc = [[dot(v,w) for w in menus[2]] for v in menus[1]]
    best, witness = -1, None
    for i, j, k in product(range(33), repeat=3):
        value = norms[0][i] + norms[1][j] + norms[2][k] + 2*(ab[i][j]+ac[i][k]+bc[j][k])
        if value > best:
            best, witness = value, [i,j,k]
    beta13 = Fraction(2*best, 9*25*13**2)
    require(beta13 == Fraction(1572,4225), "thirteen-group coefficient")
    rows7 = small_supports(7, [[0,1,2],[3,4],[5,6]])
    norm7 = max(dot(v,v) for v in rows7)
    beta7 = Fraction(2*norm7, 25*7**2)
    require(beta7 == Fraction(632,1225), "seven-group coefficient")
    print(json.dumps({'status':'PASS','thirteen_group_tuples':33**3,
                      'thirteen_group_maximum_norm_squared':best,
                      'thirteen_group_witness':witness,'beta13_squared':str(beta13),
                      'seven_group_supports':len(rows7),
                      'seven_group_maximum_norm_squared':norm7,'beta7_squared':str(beta7)},indent=2))


if __name__ == '__main__':
    main()
