"""Fresh finite semantic checks for the unrestricted-stabilization proposal.

This file is independent of all inherited builders, checkers, and executables.
It checks finite identities only; it does not construct Pell witnesses or prove
the all-integer theorem by enumeration. Python's unlimited integers are used.
"""

from collections import deque
from itertools import product
import hashlib
import json
from pathlib import Path
import random


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def geom(base, length):
    return sum(base ** i for i in range(length))


def spread(value, base, length, stride):
    require(base >= 2 and base & (base - 1) == 0, "radix domain")
    require(length >= 1 and stride >= length + 1, "spread domain")
    require(0 <= value < base ** length, "spread range")
    return (value * geom(base ** (stride - 1), length)) & (
        (base - 1) * geom(base ** stride, length)
    )


def pack(values, base):
    return sum(v * base ** j for j, v in enumerate(values))


def coord_index(coord, dims):
    x, y, z = coord
    a, b, _ = dims
    return x + a * y + a * b * z


def shift_neighbors(values, dims):
    a, b, c = dims
    out = [0] * (a * b * c)
    for x, y, z in product(range(a), range(b), range(c)):
        value = values[coord_index((x, y, z), dims)]
        if not value:
            continue
        for axis in range(3):
            for direction in (-1, 1):
                target = [x, y, z]
                target[axis] += direction
                require(0 <= target[axis] < dims[axis], "nonzero exterior flux")
                out[coord_index(target, dims)] += value
    return out


def check_packing(base, dims, values, initial, stable):
    a, b, c = dims
    n = a * b * c
    x, y = base ** a, base ** (a * b)
    interior = base * x * y * geom(base, a - 2) * geom(x, b - 2) * geom(y, c - 2)
    cap = base // 16 - 1
    count = pack(values, base)
    require(count & ~((base // 16 - 1) * interior) == 0, "count mask")
    require(count % y == 0, "negative shifts are exact")
    neighbors = shift_neighbors(values, dims)
    shift_stream = base * count + x * count + y * count + count // base + count // x + count // y
    require(shift_stream == pack(neighbors, base), "neighbor shift identity")
    lhs_coeffs = [h + w for h, w in zip(initial, neighbors)]
    rhs_coeffs = [6 * u + f for u, f in zip(values, stable)]
    require(max(lhs_coeffs) <= 20 + 6 * cap < base, "left carry bound")
    require(max(rhs_coeffs) <= 6 * cap + 5 < base, "right carry bound")
    lhs = pack(initial, base) + shift_stream
    rhs = 6 * count + pack(stable, base)
    require(lhs == pack(lhs_coeffs, base), "left positional sum")
    require(rhs == pack(rhs_coeffs, base), "right positional sum")
    require((lhs == rhs) == (lhs_coeffs == rhs_coeffs), "packed equality equivalence")
    require(lhs < base ** n and rhs < base ** n, "no top overflow")


def neighbors_of(vertex):
    for axis in range(3):
        for direction in (-1, 1):
            result = list(vertex)
            result[axis] += direction
            yield tuple(result)


def stabilize_zero_background(initial):
    heights = dict(initial)
    counts = {}
    queue = deque(v for v, height in heights.items() if height >= 6)
    in_queue = set(queue)
    steps = 0
    while queue:
        v = queue.popleft()
        in_queue.remove(v)
        while heights.get(v, 0) >= 6:
            heights[v] -= 6
            counts[v] = counts.get(v, 0) + 1
            steps += 1
            require(steps <= 10000, "finite-check safety bound")
            for w in neighbors_of(v):
                heights[w] = heights.get(w, 0) + 1
                if heights[w] >= 6 and w not in in_queue:
                    queue.append(w)
                    in_queue.add(w)
    require(all(0 <= height <= 5 for height in heights.values()), "actual stable endpoint")
    return heights, counts, steps


def main():
    rng = random.Random(20261004)
    dims = (4, 4, 4)
    inside = [coord_index(v, dims) for v in product(range(1, 3), repeat=3)]
    cases = 0
    # Exhaustive binary counts on the eight interior vertices at the weakest
    # abstract radix. The actual conversion requirements force radix >= 1024.
    for bits in product((0, 1), repeat=8):
        values = [0] * 64
        for j, value in zip(inside, bits):
            values[j] = value
        check_packing(32, dims, values, [20] * 64, [5] * 64)
        cases += 1
    # Counts reach the proposed cap, including all neighbors simultaneously.
    dims = (5, 5, 5)
    inside = [coord_index(v, dims) for v in product(range(1, 4), repeat=3)]
    for base in (32, 1024, 32768):
        cap = base // 16 - 1
        for case in range(200):
            values = [0] * 125
            for j in inside:
                values[j] = cap if case == 0 else rng.randrange(cap + 1)
            check_packing(base, dims, values,
                          [20 if case == 0 else rng.randrange(21) for _ in range(125)],
                          [5 if case == 0 else rng.randrange(6) for _ in range(125)])
            if case == 0:
                require(max(shift_neighbors(values, dims)) == 6 * cap,
                        "the six-neighbor upper bound is attained")
            cases += 1
        mask = cap * sum(base ** j for j in inside)
        for j in inside:
            require((cap * base ** j) & ~mask == 0, "cap accepted by mask")
            require(((cap + 1) * base ** j) & ~mask != 0, "first over-cap rejected")

    conversions = 0
    for length in range(1, 6):
        for extra in range(3):
            stride = length + 1 + extra
            base = 32 ** stride
            for _ in range(30):
                digits = [rng.randrange(16) for _ in range(length)]
                raw = pack(digits, 32)
                require(spread(raw, 32, length, stride) == pack(digits, base),
                        "raw physical digit preservation")
                conversions += 1

    # Valid repeated global-stabilization separator: binary counts cannot work
    # because origin initially holds 12, but its true count is 2.
    raw = 12 + 4 * 32
    exponent = 3  # >= tile length + 1 and patch length + 1
    base = 32 ** exponent
    converted = spread(raw, 32, 2, exponent)
    require(converted == 12 + 4 * base, "repeated example conversion")
    initial = {(0, 0, 0): 12, (1, 0, 0): 4}
    final, actual, steps = stabilize_zero_background(initial)
    require(actual == {(0, 0, 0): 2, (1, 0, 0): 1} and steps == 3,
            "repeated example true odometer")
    dims = (8, 4, 4)
    offset = (4, 2, 2)
    count_digits, initial_digits, final_digits = ([0] * 128 for _ in range(3))
    for source, target in ((actual, count_digits), (initial, initial_digits), (final, final_digits)):
        for v, height in source.items():
            local = tuple(v[k] + offset[k] for k in range(3))
            target[coord_index(local, dims)] = height
    check_packing(base, dims, count_digits, initial_digits, final_digits)
    require(pack(initial_digits, base) + pack(shift_neighbors(count_digits, dims), base)
            == 6 * pack(count_digits, base) + pack(final_digits, base),
            "repeated example satisfies complete packed balance")

    # A genuine accepted non-odometer supersolution. No initial site is legal.
    initial = {(0, 0, 0): 5, (1, 0, 0): 5}
    _, actual, steps = stabilize_zero_background(initial)
    require(actual == {} and steps == 0, "stable input has zero true odometer")
    inflated = {(0, 0, 0): 1, (1, 0, 0): 1}
    endpoint = dict(initial)
    for v, count in inflated.items():
        endpoint[v] = endpoint.get(v, 0) - 6 * count
        for w in neighbors_of(v):
            endpoint[w] = endpoint.get(w, 0) + count
    require(all(0 <= height <= 5 for height in endpoint.values()), "overfiring stable supersolution")

    # An explicit counterexample to dropping the x-boundary shell. Multiplying
    # the last x slot by the radix wraps to the next row instead of going outside.
    dims = (4, 4, 4)
    source = (3, 1, 1)
    wrapped = (0, 2, 1)
    require(coord_index(source, dims) + 1 == coord_index(wrapped, dims), "row wrap witness")
    require(wrapped not in set(neighbors_of(source)), "row wrap is not a lattice edge")

    receipt = {
        "status": "pass",
        "scope": "fresh independent finite mathematical checks; no inherited executable imported or run",
        "packing_cases": cases,
        "raw_conversion_cases": conversions,
        "radices_checked": [32, 1024, 32768],
        "repeated_stabilization": {"raw_D": raw, "steps": 3, "counts": [2, 1]},
        "overfiring_supersolution_demonstrated": True,
        "boundary_removal_counterexample_demonstrated": True,
        "does_not_check": ["Pell witnesses", "new polynomial source", "all-integer theorem by enumeration"],
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    output = Path(__file__).with_name("finite-check-receipt.json")
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
