#!/usr/bin/env python3
"""Replay the sextic group test .

Generators for the 16 transitive sextic groups are transcribed, in order,
from SymPy 1.14.0, S6TransitiveSubgroups.get_perm_group(). The underlying
classification is a cited input. No third-party packages are needed here.
"""

from collections import Counter

CATALOG = [
    ("C6", 6, ["123456"]),
    ("S3", 6, ["123 456", "14 26 35"]),
    ("D6", 12, ["123456", "16 25 34"]),
    ("A4", 12, ["156 243", "123 465"]),
    ("G18", 18, ["123", "456", "15 26 34"]),
    ("A4xC2", 24, ["156 243", "123 465", "35"]),
    ("S4-", 24, ["2564", "15 26 34"]),
    ("S4+", 24, ["1352 46", "14 56"]),
    ("G36-", 36, ["123", "456", "23 46", "15 26 34"]),
    ("G36+", 36, ["123", "456", "1634 25"]),
    ("S4xC2", 48, ["2564", "15 26 34", "25 46"]),
    ("PSL2(F5)", 60, ["156 243", "15426"]),
    ("G72", 72, ["123", "1524 36", "14 25 36"]),
    ("PGL2(F5)", 120, ["12345", "16 23 45"]),
    ("A6", 360, ["123", "23456"]),
    ("S6", 720, ["123456", "12"]),
]


def parse_cycles(specification):
    perm = list(range(6))
    for digits in specification.split():
        cycle = [int(digit) - 1 for digit in digits]
        for index, point in enumerate(cycle):
            perm[point] = cycle[(index + 1) % len(cycle)]
    assert sorted(perm) == list(range(6))
    return tuple(perm)


def generate_group(generators):
    identity = tuple(range(6))
    group = {identity}
    queue = [identity]
    while queue:
        element = queue.pop()
        for generator in generators:
            product = tuple(generator[x] for x in element)
            if product not in group:
                group.add(product)
                queue.append(product)
    return group


def cycle_shape(perm):
    unseen = set(range(len(perm)))
    lengths = []
    while unseen:
        point = next(iter(unseen))
        length = 0
        while point in unseen:
            unseen.remove(point)
            point = perm[point]
            length += 1
        lengths.append(length)
    return tuple(sorted(lengths))


def check():
    accepted = {}
    print("Catalog group, order, number of elements with all cycles even")
    for name, order, specifications in CATALOG:
        group = generate_group([parse_cycles(spec) for spec in specifications])
        assert len(group) == order
        assert {perm[0] for perm in group} == set(range(6))
        counts = Counter(map(cycle_shape, group))
        bad = sum(count for shape, count in counts.items()
                  if all(length % 2 == 0 for length in shape))
        print(f"{name:10s} {order:3d} {bad:3d}")
        if not bad:
            accepted[name] = dict(counts)
            assert max(min(k for k in shape if k % 2) for shape in counts) == 3
    identity = (1,) * 6
    assert accepted == {
        "A4": {identity: 1, (1, 1, 2, 2): 3, (3, 3): 8},
        "PSL2(F5)": {identity: 1, (1, 1, 2, 2): 15, (3, 3): 20, (1, 5): 24}
    }
    print("A4 and A5 cycle tables verified.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run Python without -O so all checks are active.")
    check()
