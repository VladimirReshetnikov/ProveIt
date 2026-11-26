"""Enumerate binary central events; compare a rational PSD test and the subgroup theorem."""
from itertools import permutations, product
from math import gcd
from functools import reduce
from collections import Counter


class Group:
    def __init__(self, elements, multiply):
        self.elements = list(elements)
        index = {g: i for i, g in enumerate(self.elements)}
        self.n = len(index)
        self.m = [[index[multiply(x, y)] for y in self.elements] for x in self.elements]
        assert self.m[0] == list(range(self.n))
        self.inv = [row.index(0) for row in self.m]
        self.conj = [{self.m[self.m[x][g]][self.inv[x]] for x in range(self.n)}
                     for g in range(self.n)]
        self.classes = sorted({tuple(sorted(c)) for c in self.conj})
        self.diff = [[self.m[self.inv[x]][y] for y in range(self.n)] for x in range(self.n)]

    def cosets(self, subgroup):
        return sorted({tuple(sorted(self.m[x][h] for h in subgroup)) for x in range(self.n)})


def symmetric(n, cyclic=1):
    def multiply(x, y):
        p, a = x
        q, b = y
        return tuple(p[i] for i in q), (a + b) % cyclic
    return Group(product(permutations(range(n)), range(cyclic)), multiply)


def dihedral(n):
    return Group(product(range(n), range(2)),
                 lambda x, y: ((x[0] + (-1)**x[1] * y[0]) % n, (x[1]+y[1]) % 2))


def commutators(g):
    m = g.m
    generated = {m[m[x][y]][m[g.inv[x]][g.inv[y]]] for x in range(g.n) for y in range(g.n)}
    while True:
        larger = {m[x][y] for x in generated for y in generated}
        if larger == generated:
            return larger
        generated = larger


def psd(a):
    """Fraction-free Schur complements, including singular pivots."""
    while a:
        pivot = a[0][0]
        if pivot < 0 or (pivot == 0 and any(a[0])):
            return False
        if pivot == 0:
            a = [row[1:] for row in a[1:]]
        else:
            a = [[pivot * a[i][j] - a[i][0] * a[0][j] for j in range(1, len(a))]
                 for i in range(1, len(a))]
            common = reduce(gcd, (v for row in a for v in row), 0)
            if common > 1:
                a = [[v // common for v in row] for row in a]
    return True


def subgroup_model(g, H, fibers, f):
    """Recognize an inflated event or explicitly recover K, J and its sign."""
    if all(len({f[x] for x in c}) == 1 for c in fibers):
        return 0
    if f[0] != 0:
        return None
    K = {x for x in H if f[x] == 0}
    if any(g.m[x][y] not in K for x in K for y in K):
        return None
    if any(not g.conj[x] <= K for x in K):
        return None
    kcosets = g.cosets(K)
    if any(len({f[x] for x in c}) != 1 for c in kcosets):
        return None
    special = {}
    for fiber in fibers:
        local = [c for c in kcosets if c[0] in fiber]
        zeros = [c for c in local if not f[c[0]]]
        ones = [c for c in local if f[c[0]]]
        if not zeros or not ones:
            continue
        if len(zeros) == 1:
            chosen, sign = zeros[0], 1
        elif len(ones) == 1:
            chosen, sign = ones[0], -1
        else:
            return None
        for x in chosen:
            special[x] = sign
    if 0 not in special or special[0] != 1:
        return None
    for x in special:
        if any(special.get(y) != special[x] for y in g.conj[x]):
            return None
        for y in special:
            if special.get(g.m[x][y]) != special[x] * special[y]:
                return None
    return len(special)


def run(name, g, H=None):
    H = commutators(g) if H is None else H
    assert all(g.conj[x] <= H for x in H)
    fibers = g.cosets(H)
    fc = {x: c for c in fibers for x in c}
    # A central operator is PSD iff it is PSD on the center of the group algebra:
    # each irreducible eigenvalue occurs there, on its primitive central idempotent.
    sizes = [[[0]*g.n for c in g.classes] for d in g.classes]
    for i, c in enumerate(g.classes):
        for j, d in enumerate(g.classes):
            for x in c:
                for y in d:
                    sizes[i][j][g.diff[x][y]] += 1
    distribution = Counter()
    tested = 0
    for bits in product(range(2), repeat=len(g.classes)):
        f = [0]*g.n
        for c, bit in zip(g.classes, bits):
            for x in c:
                f[x] = bit
        if any(f[x] != f[g.inv[x]] for x in range(g.n)):
            continue
        tested += 1
        kernel = [sum(f[h] for h in fc[x]) - len(H)*f[x] for x in range(g.n)]
        matrix = [[sum(a*b for a, b in zip(weights, kernel)) for weights in row] for row in sizes]
        scale = subgroup_model(g, H, fibers, f)
        assert psd(matrix) == (scale is not None), (name, f)
        if scale is None:
            continue
        # Kernel equals |H| times the classified positive multiple of a projection.
        for z in range(g.n):
            square = sum(kernel[x]*kernel[g.diff[x][z]] for x in range(g.n))
            assert square == len(H)*scale*kernel[z]
        distribution[scale] += 1
    print(f'{name:11} |G|={g.n:3} |H|={len(H):2} tested={tested:4} '
          f'admissible={sum(distribution.values()):3} by scale={dict(sorted(distribution.items()))}')


def cubic_example():
    g = symmetric(3, 2)
    f = []
    for p, c in g.elements:
        fixed = sum(p[i] == i for i in range(3))
        sgn = -1 if fixed == 1 else 1
        eta = (-1)**c
        rho = fixed - 1
        event = int((eta == 1 and fixed == 0) or (eta == -1 and fixed == 3))
        assert 12*event == 3*(1+sgn) + (1+sgn)*eta - 4*rho*eta
        f.append(event)
    assert sum(f) == 3
    print('Cubic quadratic-twist identity verified on all 12 elements; support = 3/12.')


if __name__ == '__main__':
    for n in (3, 4, 5):
        run(f'S{n}', symmetric(n))
    run('S3 x C2', symmetric(3, 2))
    run('S3 x C3', symmetric(3, 3))
    run('D8', dihedral(4))
    run('D12', dihedral(6))
    run('D16', dihedral(8))
    g = symmetric(2, 4)
    run('C2 x C4', g, {0, 2})
    run('C2 x C4', g, set(range(4)))
    cubic_example()
