"""Exhaust the marginal condition for conductor eight on small abelian groups.

Each nonempty subset is given its uniform distribution. Its affine span must
be the whole group. Character-sum checks and coset generation use integers.
Run with Python 3.10 or later. No third-party packages are needed.
"""
from itertools import product


def indices(points, values):
    return sum(1 << i for i, a in enumerate(points) if a in values)


def check_group(moduli):
    points = list(product(*(range(n) for n in moduli)))
    full = (1 << len(points)) - 1
    tests = set()
    hyperplanes = set()
    predicted = {full}
    for coeffs in points:
        values = [sum((8 // n) * c * x for c, x, n in zip(coeffs, point, moduli)) % 8
                  for point in points]
        image = set(values)
        if image == {0, 4}:
            mask = indices(values, {0})
            hyperplanes.update((mask, full ^ mask))
        if image == {0, 2, 4, 6}:
            for start in (0, 2, 4, 6):
                predicted.add(indices(values, {start, (start + 2) % 8}))
        for shift in range(8):
            # kappa_{-8} is +1 at 1 and 3, -1 at 5 and 7.
            # kappa_{+8} (the other primitive character) is its translate on
            # the odd residues, so testing all shifts covers both characters.
            positive = indices(values, {(1 - shift) % 8, (3 - shift) % 8})
            negative = indices(values, {(5 - shift) % 8, (7 - shift) % 8})
            tests.add(tuple(sorted((positive, negative))))
    accepted = set()
    spanning = 0
    for mask in range(1, full + 1):
        # A proper coset lies inside a coset of a maximal subgroup of index 2.
        if any(mask & ~h == 0 for h in hyperplanes):
            continue
        spanning += 1
        size = mask.bit_count()
        for positive, negative in tests:
            value = (mask & positive).bit_count() - (mask & negative).bit_count()
            if value and abs(value) != size:
                break
        else:
            accepted.add(mask)
    assert accepted == predicted, (moduli, accepted ^ predicted)
    return len(points), spanning, len(accepted)


if __name__ == "__main__":
    for moduli in [(2, 2, 2), (4,), (4, 2), (4, 4), (8,), (8, 2)]:
        order, spanning, accepted = check_group(moduli)
        print(f"moduli={moduli}, order={order}, spanning subsets={spanning}, "
              f"accepted and predicted={accepted}")
