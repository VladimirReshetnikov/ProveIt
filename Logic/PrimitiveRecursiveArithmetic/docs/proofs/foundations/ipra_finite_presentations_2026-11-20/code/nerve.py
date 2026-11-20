"""Exact mod-two chain checks for incidence complexes. Run python3 nerve.py."""
from fractions import Fraction
from itertools import combinations, product


def powerset_nonempty(xs):
    xs = sorted(xs)
    for r in range(1, len(xs) + 1):
        yield from combinations(xs, r)


def extend(column, chain):
    """Linear extension over F_2. Chains are sets of basis keys."""
    value = set()
    for key in chain:
        value ^= set(column(key))
    return value


def rank(columns):
    pivots = {}
    for column in columns:
        vector = set(column)
        while vector:
            pivot = max(vector)
            if pivot not in pivots:
                pivots[pivot] = vector
                break
            vector ^= pivots[pivot]
    return len(pivots)


def betti(chain):
    """Dictionary from cell to (degree, ordinary boundary)."""
    maxdim = max(deg for deg, _ in chain.values())
    ranks = [rank(b for deg, b in chain.values() if deg == k)
             for k in range(maxdim + 1)] + [0]
    return [sum(deg == k for deg, _ in chain.values()) - ranks[k] - ranks[k + 1]
            for k in range(maxdim + 1)]


def get_cone_data(cells, membership, vertical, target):
    """Compute the augmented Čech incidence complex, differential, and local h."""
    cone = {(I, c) for c, members in membership.items() for I in powerset_nonempty(members)}
    nerve = {I for I, _ in cone}
    if target == 'space':
        cone.update(((), c) for c in cells)
    else:
        cone.update((I, None) for I in nerve)

    def boundary(key):
        I, c = key
        ans = set()
        if len(I) > 1 or (target == 'space' and I):
            ans.update((I[:i] + I[i + 1:], c) for i in range(len(I)))
        if c is not None:
            deg, faces = cells[c]
            ans.update((I, f) for f in faces)
            if deg == 0 and target == 'nerve':
                ans.add((I, None))
        return ans

    def local_h(key):
        I, c = key
        if target == 'space':
            apex = min(membership[c])
            return set() if apex in I else {(tuple(sorted((*I, apex))), c)}
        return {(I, f) for f in vertical(I, c)}

    return cone, boundary, local_h, nerve


def verify(cells, membership, vertical):
    """Check d²=0 and the two global contracting-homotopy identities on all bases."""
    assert all(membership.values())
    counts = []
    for target in ('space', 'nerve'):
        cone, boundary, h, nerve = get_cone_data(cells, membership, vertical, target)
        d = {k: boundary(k) for k in cone}
        local = {k: h(k) for k in cone}
        assert all(c <= cone for c in [*d.values(), *local.values()])
        assert all(not extend(d.__getitem__, faces) for faces in d.values())
        residual = {k: {k} ^ extend(d.__getitem__, local[k]) ^ extend(local.__getitem__, d[k])
                    for k in cone}
        exponent = (1 + max(deg for deg, _ in cells.values()) if target == 'space'
                    else max(len(I) for I in nerve))
        H = {}
        for k in cone:
            term, value = {k}, set()
            for _ in range(exponent):
                value ^= extend(local.__getitem__, term)
                term = extend(residual.__getitem__, term)
            assert not term
            H[k] = value
        for k in cone:
            assert extend(d.__getitem__, H[k]) ^ extend(H.__getitem__, d[k]) == {k}
        counts.append(len(cone))
    nerve_complex = {I: (len(I)-1, {f for f in combinations(I, len(I)-1) if f})
                     for I in nerve}
    bx, bn = betti(cells), betti(nerve_complex)
    while len(bx) < len(bn):
        bx.append(0)
    while len(bn) < len(bx):
        bn.append(0)
    assert bx == bn
    return counts, bx


def rational_boxes(boxes):
    """Partition a union of closed rational boxes into its elementary cells."""
    assert boxes
    dim = len(boxes[0])
    for box in boxes:
        assert len(box) == dim and all(Fraction(a) <= Fraction(b) for a, b in box)
    coords = [sorted({Fraction(x) for B in boxes for x in B[i]}) for i in range(dim)]
    bounds = [[(2 * row.index(Fraction(lo)), 2 * row.index(Fraction(hi)))
               for row, (lo, hi) in zip(coords, B)] for B in boxes]
    cells, membership = {}, {}
    for c in product(*(range(2 * len(row) - 1) for row in coords)):
        covers = {j for j, b in enumerate(bounds) if all(lo <= k <= hi for (lo, hi), k in zip(b, c))}
        if not covers:
            continue
        faces = {c[:i] + (c[i] + s,) + c[i+1:] for i in range(dim) if c[i] % 2 for s in (-1, 1)}
        cells[c] = sum(t % 2 for t in c), faces
        membership[c] = covers

    def vertical(I, c):
        left = tuple(max(bounds[j][i][0] for j in I) for i in range(dim))
        if c is None:
            return {left}
        answer = set()
        for i in range(dim):
            if c[i] % 2:  # P_i kills an edge; later summands vanish too.
                break
            for edge in range(left[i] + 1, c[i], 2):
                answer.add(left[:i] + (edge,) + c[i+1:])
        return answer

    return verify(cells, membership, vertical)


def finite_subcomplexes(facets_by_chart):
    """Construct every augmented local contraction by exhaustive bounded filling."""
    membership = {}
    for j, chart in enumerate(facets_by_chart):
        for facet in chart:
            for c in powerset_nonempty(facet):
                membership.setdefault(c, set()).add(j)
    cells = {c: (len(c)-1, {f for f in combinations(c, len(c)-1) if f}) for c in membership}
    nerve = {I for indices in membership.values() for I in powerset_nonempty(indices)}
    fills = {}
    for I in nerve:
        local_cells = sorted((c for c, S in membership.items() if set(I) <= S), key=lambda c: (len(c), c))
        H = {None: {local_cells[0]}}
        aug = lambda c: cells[c][1] if len(c) > 1 else {None}
        for c in local_cells:
            cycle = {c} ^ extend(H.__getitem__, aug(c))
            candidates = [s for s in local_cells if len(s) == len(c) + 1]
            for mask in range(1 << len(candidates)):
                filler = {s for j, s in enumerate(candidates) if mask >> j & 1}
                if extend(aug, filler) == cycle:
                    H[c] = filler
                    break
            else:
                raise ValueError(f'acyclicity fails on intersection {I}, cell {c}')
        fills[I] = H
    return verify(cells, membership, lambda I, c: fills[I][c])


if __name__ == '__main__':
    frame = [[(0, 3), (0, 1)], [(2, 3), (0, 3)], [(0, 3), (2, 3)], [(0, 1), (0, 3)]]
    sphere = [[(v,v) if i == axis else (0,1) for i in range(3)]
              for axis in range(3) for v in (0,1)]
    cases = [('rectangular frame', frame, [1,1,0]),
             ('six faces of cube', sphere, [1,0,1]),
             ('rational endpoints', [[('1/3','2/3')],[('2/3','5/6')]], [1,0]),
             ('zero dimensions, duplicate boxes', [(), (), ()], [1,0,0])]
    for label, boxes, expected in cases:
        columns, numbers = rational_boxes(boxes)
        assert numbers == expected
        print(f'{label}: cone columns {columns}, Betti {numbers}')
    arcs = [[(0,1),(1,2),(2,3)], [(3,4),(4,5),(5,6)], [(6,7),(7,8),(8,0)]]
    columns, numbers = finite_subcomplexes(arcs)
    assert numbers == [1,1]
    print(f'three paths: cone columns {columns}, Betti {numbers}')
    try:
        finite_subcomplexes([[(0,1),(1,2)], [(2,3),(3,0)]])
    except ValueError as err:
        assert 'intersection (0, 1)' in str(err)
        print(f'disconnected overlap correctly rejected: {err}')
    else:
        raise AssertionError('disconnected overlap accepted')
