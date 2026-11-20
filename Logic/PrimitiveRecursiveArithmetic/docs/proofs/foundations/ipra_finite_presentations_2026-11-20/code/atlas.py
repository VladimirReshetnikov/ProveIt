"""Exact margin of a finite union of rational affine charts on a unit cube."""
from fractions import Fraction as Q
from itertools import combinations, permutations, product
from math import prod


def determinant(rows):
    n = len(rows)
    total = 0
    for perm in permutations(range(n)):
        inversions = sum(perm[i] > perm[j] for i, j in combinations(range(n), 2))
        total += (-1)**inversions * prod(rows[i][perm[i]] for i in range(n))
    return total


def solve(equations, d):
    rows = [row[:d] for row in equations]
    denominator = determinant(rows)
    if not denominator:
        return None
    answer = []
    for column in range(d):
        sub = [tuple(-equations[i][d] if j == column else rows[i][j]
                     for j in range(d)) for i in range(d)]
        answer.append(Q(determinant(sub), denominator))
    return tuple(answer)


def value(affine, x):
    return affine[-1] + sum(a * v for a, v in zip(affine[:-1], x))


def slack(charts, x):
    return max(min(value(l, x) for l in chart) for chart in charts)


def minimum(charts, d):
    atoms = [l for chart in charts for l in chart]
    planes = [tuple(a-b for a, b in zip(u, v)) for u, v in combinations(atoms, 2)]
    for j in range(d):
        unit = tuple(int(j == i) for i in range(d))
        planes.extend((unit + (0,), unit + (-1,)))
    vertices = set()
    for equations in combinations(planes, d):
        x = solve(equations, d)
        if x is not None and all(0 <= t <= 1 for t in x):
            vertices.add(x)
    return min((slack(charts, x), x) for x in vertices)


def self_check():
    # On each coordinate either low (<2/3) or high (>1/3).
    charts = []
    for sx, sy in product(range(2), repeat=2):
        charts.append([(-1,0,Q(2,3)) if sx == 0 else (1,0,-Q(1,3)),
                       (0,-1,Q(2,3)) if sy == 0 else (0,1,-Q(1,3))])
    mu, witness = minimum(charts, 2)
    assert mu == Q(1, 6) and slack(charts, witness) == mu
    # A piecewise-linear path z(t)=t+i(2t-1). Target {0,1}.
    # Four signed coordinate differences for each puncture; distribute
    # min(max(A),max(B)) = max_{i,j} min(A_i,B_j).
    zero = [(1,0),(-1,0),(2,-1),(-2,1)]
    one = [(1,-1),(-1,1),(2,-1),(-2,1)]
    path_charts = list(product(zero, one))
    clearance, nearest = minimum(path_charts, 1)
    assert clearance == Q(1, 3) and nearest == (Q(1, 3),)
    assert minimum([[(1,0)], [(-1,0)]], 1)[0] == 0
    assert minimum([[(-1,-1)]], 1)[0] == -2
    assert minimum([[(Q(3,4),)]], 0)[0] == Q(3,4)
    print(f"atlas: square margin {mu}, witness {witness}; punctured path clearance {clearance}")


if __name__ == "__main__":
    self_check()
