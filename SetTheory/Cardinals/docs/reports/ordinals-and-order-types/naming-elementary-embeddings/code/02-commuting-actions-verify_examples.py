#!/usr/bin/env python3
"""Deterministic finite checks for Commuting Actions and Replacement.

Run with Python 3.10 or newer:
    python3 verify_examples.py

The printed report is the deliverable verification_output.txt when redirected.
All mathematical checks use integers and finite sets. This program does not
verify any infinite theorem, forcing argument, class model, or axiom scheme.
Its truncated staircase comparisons are finite shadows only.
"""

from collections import Counter
from itertools import product


COUNTS = Counter()


def require(condition, category):
    """An explicit check which remains active under python -O."""
    if not condition:
        raise AssertionError("Finite check failed: " + category)
    COUNTS[category] += 1


def drop(mask, m):
    if m < 0:
        return 1
    if m == 0:
        return 3
    return 1 + ((mask >> (m - 1)) & 1)


def height(mask, m):
    """h(0)=0 and h(m+1)=h(m)-d(m), evaluated by finite sums."""
    if m < 0:
        return sum(drop(mask, j) for j in range(m, 0))
    return -sum(drop(mask, j) for j in range(0, m))


def move_f(point):
    return (point[0] + 1, point[1])


def move_g(point):
    return (point[0], point[1] + 1)


def in_staircase(mask, point):
    return point[1] >= height(mask, point[0])


def verify_staircases():
    masks = range(1 << 8)
    for mask in masks:
        require(height(mask, 0) == 0, "staircase origin")
        decoded = 0
        for m in range(-8, 18):
            actual = height(mask, m) - height(mask, m + 1)
            require(actual > 0, "strict boundary decrease")
            require(actual == drop(mask, m), "drop recurrence")
            require((actual == 3) == (m == 0), "unique marker drop")
        for bit in range(8):
            value = height(mask, bit + 1) - height(mask, bit + 2) - 1
            require(value in (0, 1), "decoded binary value")
            decoded |= value << bit
        require(decoded == mask, "eight-bit decoding round trip")

        points = []
        for m in range(-6, 13):
            boundary = height(mask, m)
            for offset in range(6):
                point = (m, boundary + offset)
                points.append(point)
                require(in_staircase(mask, move_f(point)), "f preserves staircase")
                require(in_staircase(mask, move_g(point)), "g preserves staircase")
                require(move_f(move_g(point)) == move_g(move_f(point)),
                        "coordinate maps commute")
            require(not in_staircase(mask, (m, boundary - 1)),
                    "vertical boundary has no predecessor")
        require(len({move_f(p) for p in points}) == len(points),
                "finite f injectivity")
        require(len({move_g(p) for p in points}) == len(points),
                "finite g injectivity")

        # A sufficiently broad finite interval crosses the horizontal start of
        # each displayed row. This is a finite ray-pattern check, not a proof
        # about all rows of the infinite staircase.
        for n in range(-18, 13):
            row = [m for m in range(-40, 41) if in_staircase(mask, (m, n))]
            require(bool(row) and row[0] > -40, "row start lies in test window")
            require(row == list(range(row[0], 41)), "finite horizontal ray pattern")
            require(not in_staircase(mask, (row[0] - 1, n)),
                    "horizontal boundary has no predecessor")

    # Exact translated boundary words. The window includes every encoded bit
    # and the marker for every tested shift. Unchecked shifts are not tested.
    columns = tuple(range(-10, 19))
    original = {}
    for mask in masks:
        word = tuple(height(mask, m) for m in columns)
        require(word not in original, "distinct finite boundary shadows")
        original[word] = mask
    for mask in masks:
        for horizontal in range(-4, 5):
            shifted = tuple(height(mask, m + horizontal) for m in columns)
            for vertical in range(-12, 13):
                word = tuple(value + vertical for value in shifted)
                match = original.get(word)
                expected = mask if horizontal == 0 and vertical == 0 else None
                require(match == expected, "finite translated-shadow comparison")


MODULUS = 4
ABELIAN_GROUP = tuple(product(range(MODULUS), repeat=2))
ZERO = (0, 0)


def add(x, y):
    return ((x[0] + y[0]) % MODULUS, (x[1] + y[1]) % MODULUS)


def generate_subgroup(generators):
    result = {ZERO}
    pending = [ZERO]
    while pending:
        x = pending.pop()
        for generator in generators:
            y = add(x, generator)
            if y not in result:
                result.add(y)
                pending.append(y)
    return frozenset(result)


def all_subgroups():
    """Enumerate the whole finite subgroup lattice by adjoining generators."""
    trivial = frozenset({ZERO})
    found = {trivial}
    pending = [trivial]
    while pending:
        subgroup = pending.pop()
        for element in ABELIAN_GROUP:
            extension = generate_subgroup(tuple(subgroup) + (element,))
            if extension not in found:
                found.add(extension)
                pending.append(extension)
    return sorted(found, key=lambda h: (len(h), sorted(h)))


def quotient(subgroup):
    return sorted({frozenset(add(x, h) for h in subgroup)
                   for x in ABELIAN_GROUP}, key=lambda c: sorted(c))


def act(element, coset):
    return frozenset(add(element, x) for x in coset)


def verify_finite_abelian_actions():
    subgroups = all_subgroups()
    require(len(subgroups) == 15, "subgroup count for (Z/4)^2")
    quotients = {h: quotient(h) for h in subgroups}
    for subgroup in subgroups:
        require(ZERO in subgroup, "subgroup identity")
        for x, y in product(subgroup, repeat=2):
            require(add(x, y) in subgroup, "subgroup closure")
        cosets = quotients[subgroup]
        require(sum(map(len, cosets)) == len(ABELIAN_GROUP), "coset partition size")
        require(set().union(*cosets) == set(ABELIAN_GROUP), "coset partition covers")
        for coset in cosets:
            stabilizer = frozenset(g for g in ABELIAN_GROUP if act(g, coset) == coset)
            require(stabilizer == subgroup, "abelian coset stabilizer")
            require(act((1, 0), act((0, 1), coset)) ==
                    act((0, 1), act((1, 0), coset)), "quotient generators commute")
            for g, h in product(ABELIAN_GROUP, repeat=2):
                require(act(g, act(h, coset)) == act(add(g, h), coset),
                        "finite quotient action law")

    # A map from a transitive action is determined by the image of its base
    # coset. We check all base-image candidates and all source representatives.
    for source_subgroup, target_subgroup in product(subgroups, repeat=2):
        source = quotients[source_subgroup]
        target = quotients[target_subgroup]
        accepted = 0
        for image_of_base in target:
            images = {}
            well_defined = True
            for coset in source:
                candidates = {act(x, image_of_base) for x in coset}
                if len(candidates) != 1:
                    well_defined = False
                    break
                images[coset] = next(iter(candidates))
            require(well_defined == (source_subgroup <= target_subgroup),
                    "quotient-map existence criterion")
            if not well_defined:
                continue
            accepted += 1
            for g, coset in product(ABELIAN_GROUP, source):
                require(images[act(g, coset)] == act(g, images[coset]),
                        "finite quotient-map equivariance")
            is_bijection = len(set(images.values())) == len(source) == len(target)
            require(is_bijection == (source_subgroup == target_subgroup),
                    "abelian transitive-type distinction")
        expected = len(target) if source_subgroup <= target_subgroup else 0
        require(accepted == expected, "finite equivariant-map count")


def verify_binary_characters():
    """Finite shadow of index-two kernels in a countable direct sum."""
    dimension = 5
    vectors = range(1 << dimension)
    kernels = {}
    for character in range(1, 1 << dimension):
        def value(x):
            return (character & x).bit_count() % 2
        kernel = frozenset(x for x in vectors if value(x) == 0)
        require(len(kernel) == 1 << (dimension - 1), "binary character kernel index")
        require(kernel not in kernels, "distinct nonzero characters have distinct kernels")
        kernels[kernel] = character
        for x, y in product(vectors, repeat=2):
            require(value(x ^ y) == (value(x) + value(y)) % 2,
                    "binary character homomorphism")
        for point in (0, 1):
            stabilizer = frozenset(x for x in vectors if (point + value(x)) % 2 == point)
            require(stabilizer == kernel, "binary quotient-point stabilizer")
            for x, y in product(vectors, repeat=2):
                require((point + value(x) + value(y)) % 2 ==
                        (point + value(x ^ y)) % 2, "binary quotient action law")


def main():
    verify_staircases()
    verify_finite_abelian_actions()
    verify_binary_characters()
    print("COMMUTING ACTIONS AND REPLACEMENT: EXACT FINITE CHECKS")
    print("Result: PASS")
    print("Arithmetic: integers and finite sets only; deterministic; no random seed.")
    print("Staircases: all 256 eight-bit prefixes, continued by zeros.")
    print("Translated boundary shadows: columns -10..18; shifts -4..4 and -12..12.")
    print("Finite abelian group: all 15 subgroups of (Z/4Z)^2.")
    print("Binary characters: all 31 nonzero characters of (F_2)^5.")
    print()
    for name, count in sorted(COUNTS.items()):
        print(f"{name}: {count:,}")
    print(f"TOTAL EXPLICIT CHECKS: {sum(COUNTS.values()):,}")
    print()
    print("SCOPE: finite sanity checks only, including finite shadows of the staircases.")
    print("This is not a formal verification or a proof of any infinite classification,")
    print("Replacement, Collection, reflection, or any class-model construction.")
    print("All checks remain active when Python is run with -O.")


if __name__ == "__main__":
    main()
