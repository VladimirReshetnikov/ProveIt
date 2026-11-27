"""Exact checks of the bounded-edit table repair. Uses only Python 3.8+."""

from collections import Counter, defaultdict
from itertools import combinations, product
from math import gcd, prod
from random import Random


def margins(table):
    return tuple(map(sum, table)), tuple(map(sum, zip(*table)))


def l1(a, b):
    return sum(abs(x-y) for ar, br in zip(a, b) for x, y in zip(ar, br))


def repair(source, witness, e):
    """Return L1 change, row deletions, column deletions, and additions."""
    k, d = len(source), len(source[0])
    assert margins(source) == margins(witness)
    sigma = [[x % e for x in row] for row in witness]
    rows, cols = margins([[x // e for x in row] for row in witness])
    z = [[max(0, (x-s)//e) for x, s in zip(a, b)] for a, b in zip(source, sigma)]
    def reconstruct():
        return [[s+e*x for s, x in zip(sr, zr)] for sr, zr in zip(sigma, z)]
    assert l1(reconstruct(), source) <= e*k*d
    for actual, target in zip(margins(z), (rows, cols)):
        assert sum(abs(x-y) for x, y in zip(actual, target)) <= k*d

    row_deleted = col_deleted = additions = 0
    for i in range(k):
        surplus = max(0, sum(z[i])-rows[i])
        for j in range(d):
            remove = min(surplus, z[i][j])
            z[i][j] -= remove
            surplus -= remove
            row_deleted += remove
    for j in range(d):
        surplus = max(0, sum(z[i][j] for i in range(k))-cols[j])
        for i in range(k):
            remove = min(surplus, z[i][j])
            z[i][j] -= remove
            surplus -= remove
            col_deleted += remove
    actual_rows, actual_cols = margins(z)
    col_deficits = [t-x for t, x in zip(cols, actual_cols)]
    for i, target in enumerate(rows):
        deficit = target - actual_rows[i]
        for j in range(d):
            add = min(deficit, col_deficits[j])
            assert add >= 0
            z[i][j] += add
            deficit -= add
            col_deficits[j] -= add
            additions += add
    assert row_deleted <= k*d and col_deleted <= k*d and additions <= 3*k*d
    fixed = reconstruct()
    assert margins(fixed) == margins(source)
    assert min(min(row) for row in fixed) >= 0
    assert all((x-y) % e == 0 for a,b in zip(fixed,witness) for x,y in zip(a,b))
    change = l1(fixed, source)
    assert change <= 6*e*k*d and change % 2 == 0
    return change, row_deleted, col_deleted, additions


def compositions(total, width):
    if width == 1:
        yield (total,)
        return
    for first in range(total+1):
        for rest in compositions(total-first, width-1):
            yield (first,) + rest


def exhaustive(k, d, e, row_sum):
    groups = defaultdict(list)
    for table in product(compositions(row_sum, d), repeat=k):
        groups[margins(table)[1]].append(table)
    pairs, maxima = 0, (0, 0, 0, 0)
    for group in groups.values():
        for source, witness in product(group, repeat=2):
            stats = repair(source, witness, e)
            maxima = tuple(map(max, zip(maxima, stats)))
            pairs += 1
    print(f"  k={k}, d={d}, e={e}, row sum={row_sum}: "
          f"{pairs} ordered pairs; maxima {maxima}")


def large_example(k, d, e, seed):
    rng = Random(seed)
    # Begin with rows concentrated in a single color, then shuffle all
    # slots to produce a distant witness with the same two margins.
    source = [[0]*d for _ in range(k)]
    for i, row in enumerate(source):
        row[i % d] = 1000 + rng.randrange(201)
    slots = [j for row in source for j, n in enumerate(row) for _ in range(n)]
    rng.shuffle(slots)
    start, witness = 0, []
    for row in source:
        end = start + sum(row)
        c = Counter(slots[start:end])
        witness.append([c[j] for j in range(d)])
        start = end
    delta, dr, dc, adds = repair(source, witness, e)
    print(f"  k={k}, d={d}, e={e}: original L1={l1(source,witness)}, "
          f"repaired L1={delta}, moved labels={delta//2}, stages=({dr},{dc},{adds})")


def mixed_example():
    pool = (2,11,13,17,19,23,29,31,37,41,43,47,53,59)
    moduli = (15, 21)
    total = prod(pool)
    counts = Counter()
    for block in combinations(pool, 7):
        p = prod(block)
        counts[(p % 15, (total//p) % 21)] += 1
    expected = {(a,b) for a in range(15) for b in range(21)
                if gcd(a,15) == gcd(b,21) == 1 and (a*b-total) % 3 == 0}
    assert set(counts) == expected
    print(f"Mixed moduli {moduli}, gcd=3: {sum(counts.values())} partitions "
          f"hit all {len(expected)} allowed pairs out of 96; total mod 3={total%3}.")
    print(f"  Counts per allowed pair: {min(counts.values())}..{max(counts.values())}.")


if __name__ == "__main__":
    print("All ordered pairs with equal margins; maxima are (L1, row removals, column removals, fills).")
    for args in ((3,2,2,3), (2,3,3,5), (2,4,2,4), (2,4,4,4)):
        exhaustive(*args)
    print("Deterministic many-row inputs:")
    for args in ((17,3,3,1), (31,4,4,2), (64,4,2,3)):
        large_example(*args)
    mixed_example()
