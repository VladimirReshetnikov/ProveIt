"""A small independent integer-only certificate checker (no imports from the library).

Checks membership, the counterexample inequality, and minimality using
finite-word minima. All comparisons below use the exact positive sqrt(21).
"""

def sign(a, b):
    # Sign of a + b*q, q = (sqrt(21)-3)/2.
    a = 2*a - 3*b
    if b == 0:
        return (a > 0) - (a < 0)
    if a == 0:
        return (b > 0) - (b < 0)
    if a*b > 0:
        return (a > 0) - (a < 0)
    difference = a*a - 21*b*b
    return ((difference > 0) - (difference < 0)) * ((a > 0) - (a < 0))


def lower(x, y):
    if x is None:
        return y
    if y is None:
        return x
    return x if sign(x[0]-y[0], x[1]-y[1]) <= 0 else y


def join(u, v):
    # (zeros, ones, minimum prefix weight immediately before a 1)
    z, o, minimum = u
    zz, oo, other_minimum = v
    if other_minimum is not None:
        other_minimum = (z+other_minimum[0], -o+other_minimum[1])
    return z+zz, o+oo, lower(minimum, other_minimum)


def prefix_counts(length):
    # Separate count-only implementation, using a list of child blocks.
    counts = {-1: (1, 0), 0: (0, 1)}
    k = 0
    while sum(counts[k]) < length:
        k += 1
        a, b = counts[k-1], counts[k-2]
        counts[k] = (3*(a[0]+b[0]), 3*(a[1]+b[1]))
    z = o = 0
    while length:
        if length == sum(counts[k]):
            return z+counts[k][0], o+counts[k][1]
        for child in [k-1, k-2]*3:
            a = counts[child]
            if length < sum(a):
                k = child
                break
            z += a[0]
            o += a[1]
            length -= sum(a)
            if not length:
                return z, o
    return z, o


def verify():
    blocks = {-1: (1, 0, None), 0: (0, 1, (0, 0))}
    for k in range(1, 12):
        pair = join(blocks[k-1], blocks[k-2])
        blocks[k] = join(join(pair, pair), pair)
    p = (0, 0, None)
    for k in [11, 10, 10, 8, 6, 4, 2]:
        p = join(p, blocks[k])
    assert p == (2356272, 2977770, (431712, -545583))
    assert prefix_counts(5334042) == (2356272, 2977770)
    assert prefix_counts(5334043) == (2356272, 2977771)
    assert prefix_counts(20222897) == (8933312, 11289585)
    assert prefix_counts(20222898) == (8933313, 11289585)
    # Every earlier 1 has E_1 <= 545584*q - 431712 < 2.
    assert sign(-431714, 545584) < 0
    assert 2500180**2 - 21*545584**2 == 110224
    # The candidate has E_1 = 2977771*q - 2356272 > 2.
    assert sign(-2356274, 2977771) > 0
    assert 21*2977771**2 - 13645861**2 == 265940
    assert 21*8933313**2 - 40937583**2 == 2393460
    return {"first_one_rank": 2977771, "first_one_position": 5334043,
            "first_zero_rank": 8933313, "first_zero_position": 20222898}


if __name__ == "__main__":
    print(verify())
    print("Independent exact certificate check: PASS")
