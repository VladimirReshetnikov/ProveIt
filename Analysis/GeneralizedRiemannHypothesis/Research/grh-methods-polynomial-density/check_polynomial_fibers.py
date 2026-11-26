"""Exhaust a small binary-polynomial instance of the confinement and counting lemmas.

This uses a small AP-free degree change that adds and removes elements.
The separate centered sphere supplies the strict asymptotic gain in the theorem.
Each nonzero bit string represents its polynomial over F_2.
"""
from collections import Counter


def multiply(f, g):
    result = 0
    while g:
        if g & 1:
            result ^= f
        g >>= 1
        f <<= 1
    return result


def in_ternary_set(value):
    while value:
        if value % 3 == 2:
            return False
        value //= 3
    return True


def check():
    n, r, m = 15, 5, 9
    def degree(f):
        return f.bit_length() - 1

    limit = 1 << (n + 1)
    smallest = [0] * limit
    for prime in range(2, limit):
        if smallest[prime] != 0:
            continue
        for quotient in range(1, 1 << (n - degree(prime) + 1)):
            product = multiply(prime, quotient)
            if smallest[product] == 0:
                smallest[product] = (prime, quotient)
    rough = [1] * limit
    squarefree_rough = [True] * limit
    smooth_counts = Counter({0: 1})
    for f in range(2, limit):
        prime, quotient = smallest[f]
        rough[f] = rough[quotient]
        squarefree_rough[f] = squarefree_rough[quotient]
        if degree(prime) > m:
            rough[f] = multiply(rough[f], prime)
            if quotient > 1 and smallest[quotient][0] == prime:
                squarefree_rough[f] = False
        if rough[f] == 1:
            smooth_counts[degree(f)] += 1

    replacement = {0, 2, 3}
    displaced = {d for d in range(m) if in_ternary_set(d)}
    original = {f for f in range(1, limit) if in_ternary_set(n - degree(f))}
    result = set()
    for f in range(1, limit):
        d = n - degree(f)
        changed = degree(rough[f]) == n - r and squarefree_rough[f] and d < m
        selected = d in replacement if changed else f in original
        if selected:
            result.add(f)
    cores = {rough[f] for f in range(1, limit)
             if degree(rough[f]) == n - r and squarefree_rough[f]}
    delta = (sum(smooth_counts[r-d] for d in replacement)
             - sum(smooth_counts[r-d] for d in displaced))
    assert len(result) - len(original) == delta * len(cores)
    assert result - original and original - result
    triples = incident = 0
    added = result - original
    for ratio in range(2, 1 << (n // 2 + 1)):
        for first in range(1, 1 << (n - 2 * degree(ratio) + 1)):
            middle = multiply(first, ratio)
            last = multiply(middle, ratio)
            triple = {first, middle, last}
            assert not triple <= result
            if triple & added:
                incident += 1
                assert rough[first] == rough[middle] == rough[last]
            triples += 1
    print(f'F_2[x], degree cutoff {n}, {len(cores)} modified rough parts')
    print(f'{len(added)} added, {len(original-result)} removed; exact change {delta} per class')
    print(f'{triples} triples checked, {incident} incident to an added polynomial')


if __name__ == '__main__':
    check()
