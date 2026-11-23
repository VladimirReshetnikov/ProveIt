"""Finite regression checks for the graph, homology, and surface chapter.

Run with Python 3. Integer checks use generic Smith reduction on the actual
signed incidence matrices of polygon fans. Binary simplicial checks build
face tables directly. These computations exercise examples of the proofs.
"""

from itertools import product
from math import gcd


def smith_diagonal(rows):
    """Nonzero Smith factors by integer row and column operations."""
    matrix = [list(row) for row in rows]
    height = len(matrix)
    width = len(matrix[0]) if height else 0
    factors = []
    for k in range(min(height, width)):
        location = next(
            ((i, j) for i in range(k, height) for j in range(k, width)
             if matrix[i][j]), None
        )
        if location is None:
            break
        i, j = location
        matrix[k], matrix[i] = matrix[i], matrix[k]
        for row in matrix:
            row[k], row[j] = row[j], row[k]

        while True:
            if matrix[k][k] < 0:
                matrix[k] = [-value for value in matrix[k]]
            pivot = matrix[k][k]
            changed = False
            for i in range(k + 1, height):
                if matrix[i][k]:
                    q = matrix[i][k] // pivot
                    matrix[i] = [a - q*b for a, b in zip(matrix[i], matrix[k])]
                    if matrix[i][k]:
                        matrix[i], matrix[k] = matrix[k], matrix[i]
                    changed = True
                    break
            if changed:
                continue
            for j in range(k + 1, width):
                if matrix[k][j]:
                    q = matrix[k][j] // pivot
                    for row in matrix:
                        row[j] -= q * row[k]
                    if matrix[k][j]:
                        for row in matrix:
                            row[j], row[k] = row[k], row[j]
                    changed = True
                    break
            if changed:
                continue

            # A nondivisible entry can be moved into the pivot row. The
            # next column reduction then gives a strictly smaller pivot.
            bad_row = next(
                (i for i in range(k + 1, height)
                 if any(x % pivot for x in matrix[i][k + 1:])), None
            )
            if bad_row is None:
                break
            matrix[k] = [a + b for a, b in zip(matrix[k], matrix[bad_row])]
        factors.append(matrix[k][k])
    assert all(b % a == 0 for a, b in zip(factors, factors[1:]))
    return factors


def polygon_fan(word):
    """Signed incidence from side identifications, retaining corner classes."""
    length = len(word)
    labels = sorted(set(map(abs, word)))
    label_index = {label: j for j, label in enumerate(labels)}
    parent = list(range(length))

    def root(i):
        while parent[i] != i:
            i = parent[i]
        return i

    def identify(a, b):
        parent[root(a)] = root(b)

    first_side = {}
    for i, letter in enumerate(word):
        ends = (i, (i + 1) % length)
        if letter < 0:
            ends = ends[::-1]
        label = abs(letter)
        if label in first_side:
            start, finish = first_side[label]
            identify(start, ends[0])
            identify(finish, ends[1])
        else:
            first_side[label] = ends

    # Vertex 0 is the center, followed by distinct glued corners.
    corners = sorted({root(i) for i in range(length)})
    corner_id = {corner: j + 1 for j, corner in enumerate(corners)}
    vertex = [corner_id[root(i)] for i in range(length)]
    edge_count = length + len(labels)
    d1 = [[0] * edge_count for _ in range(1 + len(corners))]
    d2 = [[0] * length for _ in range(edge_count)]
    for i, letter in enumerate(word):
        d1[0][i] -= 1
        d1[vertex[i]][i] += 1
        d2[i][i] += 1
        d2[(i + 1) % length][i] -= 1
        j = length + label_index[abs(letter)]
        d2[j][i] += 1 if letter > 0 else -1
    for letter, (start, finish) in first_side.items():
        j = length + label_index[letter]
        d1[vertex[start]][j] -= 1
        d1[vertex[finish]][j] += 1
    return d1, d2


def homology_signature(d1, d2):
    """Free ranks, then torsion factors of H0 and H1; C3 is zero."""
    assert all(sum(a*b for a, b in zip(row, column)) == 0
               for row in d1 for column in zip(*d2))
    s1 = smith_diagonal(d1)
    s2 = smith_diagonal(d2)
    # coker(d2) maps onto im(d1) with kernel H1. The image is free,
    # so all torsion of coker(d2) belongs to H1.
    betti = (len(d1) - len(s1), len(d2) - len(s1) - len(s2),
             len(d2[0]) - len(s2))
    return betti, [k for k in s1 if k > 1], [k for k in s2 if k > 1]


def all_subfaces(face):
    subface = face
    while subface:
        yield subface
        subface = (subface - 1) & face


def complex_from_facets(facets):
    return {face for facet in facets for face in all_subfaces(facet)}


def binary_rank(columns):
    basis = {}
    for x in columns:
        while x:
            pivot = x.bit_length()
            if pivot not in basis:
                basis[pivot] = x
                break
            x ^= basis[pivot]
    return len(basis)


def binary_betti(faces):
    if not faces:
        return ()
    layers = [sorted(f for f in faces if f.bit_count() == degree + 1)
              for degree in range(max(f.bit_count() for f in faces))]
    ranks = [0]
    for lower, upper in zip(layers, layers[1:]):
        index = {f: i for i, f in enumerate(lower)}
        columns = []
        for face in upper:
            boundary = 0
            bits = face
            while bits:
                bit = bits & -bits
                boundary ^= 1 << index[face ^ bit]
                bits ^= bit
            columns.append(boundary)
        ranks.append(binary_rank(columns))
    ranks.append(0)
    return tuple(len(layer) - left - right for layer, left, right in
                 zip(layers, ranks, ranks[1:]))


def subdivision(faces):
    nodes = sorted(faces)
    chains = [set() for _ in nodes]
    for j, face in enumerate(nodes):
        chains[j].add(1 << j)
        for i, subface in enumerate(nodes[:j]):
            if subface & face == subface:
                chains[j].update(chain | (1 << j) for chain in chains[i])
    return set().union(*chains)


def check_surfaces():
    checks = 0
    for handles, crosscaps in product(range(4), range(5)):
        if not handles and not crosscaps:
            continue
        word = []
        for k in range(handles):
            a, b = 2*k + 1, 2*k + 2
            word.extend([a, b, -a, -b])
        for k in range(crosscaps):
            y = 2*handles + k + 1
            word.extend([y, y])
        expected = ((1, 2*handles + max(0, crosscaps - 1),
                     int(not crosscaps)), [], [2] if crosscaps else [])
        # Cut the cyclic polygon at each letter and also reverse it.
        for k in range(len(word)):
            shifted = word[k:] + word[:k]
            for model in (shifted, [-a for a in reversed(shifted)]):
                d1, d2 = polygon_fan(model)
                assert homology_signature(d1, d2) == expected
                assert len(d1) - len(d2) + len(model) == 2 - 2*handles - crosscaps
                checks += 1
    assert homology_signature(*polygon_fan([1, 2, -1, 2])) == (
        (1, 1, 0), [], [2]
    )
    return checks + 1


def check_binary_homology():
    # Compare every four-vertex complex to its barycentric subdivision.
    seen = set()
    for selected in range(1 << 15):
        facets = [i + 1 for i in range(15) if selected >> i & 1]
        faces = frozenset(complex_from_facets(facets))
        if faces in seen:
            continue
        seen.add(faces)
        betti = binary_betti(faces)
        assert betti == binary_betti(subdivision(faces))
        euler = sum((-1)**(f.bit_count() - 1) for f in faces)
        assert euler == sum((-1)**k * b for k, b in enumerate(betti))

    # Check transpose duality for all labelled 3-by-3 relations.
    for relation in range(1 << 9):
        rows = [(relation >> (3*i)) & 7 for i in range(3)]
        columns = [sum(((row >> j) & 1) << i for i, row in enumerate(rows))
                   for j in range(3)]
        left = binary_betti(complex_from_facets(rows))
        right = binary_betti(complex_from_facets(columns))
        # The complexes can have different dimensions and trailing zero ranks.
        length = max(len(left), len(right))
        assert left + (0,)*(length - len(left)) == right + (0,)*(length - len(right))
    return len(seen), 1 << 9


def check_smith():
    # Independent determinantal divisors for all small 2-by-2 matrices.
    for a, b, c, d in product(range(-2, 3), repeat=4):
        divisor = gcd(a, b, c, d)
        determinant = abs(a*d - b*c)
        expected = [] if divisor == 0 else [divisor]
        if determinant:
            expected.append(determinant // divisor)
        assert smith_diagonal([[a, b], [c, d]]) == expected
    assert smith_diagonal([[6, 0], [0, 10]]) == [2, 30]


def apply_binary(columns, vector):
    image = 0
    while vector:
        bit = vector & -vector
        image ^= columns[bit.bit_length() - 1]
        vector ^= bit
    return image


def mix_bits(vector, dimension, inverse=False):
    # Each elementary addition of one coordinate to the next is involutive.
    steps = range(dimension - 1)
    for i in reversed(steps) if inverse else steps:
        vector ^= ((vector >> i) & 1) << (i + 1)
    return vector


def check_barcodes():
    stages = 4
    intervals = [(b, d) for b in range(stages) for d in range(b, stages)]
    for mask in range(1 << len(intervals)):
        bars = [bar for j, bar in enumerate(intervals) if mask >> j & 1]
        if bars:
            bars.append(bars[0])  # Test multiplicities greater than one.
        active = [[t for t, (b, d) in enumerate(bars) if b <= i <= d]
                  for i in range(stages)]
        arrows = []
        for before, after in zip(active, active[1:]):
            raw = [1 << after.index(bar_id) if bar_id in after else 0
                   for bar_id in before]
            columns = []
            for j in range(len(before)):
                source = mix_bits(1 << j, len(before), inverse=True)
                columns.append(mix_bits(apply_binary(raw, source), len(after)))
            arrows.append(columns)
        ranks = {}
        for i in range(stages):
            vectors = [1 << j for j in range(len(active[i]))]
            for j in range(i, stages):
                ranks[i, j] = binary_rank(vectors)
                if j + 1 < stages:
                    vectors = [apply_binary(arrows[j], x) for x in vectors]
        for b, d in intervals:
            count = (ranks[b, d] - ranks.get((b - 1, d), 0)
                     - ranks.get((b, d + 1), 0) + ranks.get((b - 1, d + 1), 0))
            assert count == bars.count((b, d))
    return 1 << len(intervals)


if __name__ == "__main__":
    check_smith()
    surfaces = check_surfaces()
    complexes, relations = check_binary_homology()
    barcodes = check_barcodes()
    print(f"Passed {surfaces} signed surface tests, {complexes} subdivision tests,"
          f" {relations} relation-duality tests, and {barcodes} barcode tests, plus Smith factor checks.")
