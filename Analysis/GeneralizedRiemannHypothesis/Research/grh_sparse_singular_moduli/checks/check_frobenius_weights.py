"""Exact finite checks for the support and minimax theorem, using only Python."""
from fractions import Fraction
from itertools import product
from math import isqrt


def check_group(name, sizes, derived_classes, nonlinear_rows, inverse_pairs=()):
    """Enumerate normalized class weights with ordinates 0, 1/2 and 1."""
    group_order = sum(sizes)
    best = Fraction(-2)
    maximizers = []
    checked = 0
    strict = 0
    for ordinates in product(range(3), repeat=len(sizes) - 1):
        f = (0,) + ordinates  # the actual weight is f[i]/2
        if any(f[i] != f[j] for i, j in inverse_pairs):
            continue
        c = [Fraction(-sum(m * y * z for m, y, z in zip(sizes, f, row)),
                      2 * group_order) for row in nonlinear_rows]
        if min(c) < 0:
            continue
        checked += 1
        for j in derived_classes:
            # By unitarity, chi(u)=chi(1) is equivalent to u in ker chi.
            kernel = all(k == 0 or row[j] == row[0]
                         for k, row in zip(c, nonlinear_rows))
            assert (f[j] == 0) == kernel
        response = min(k / row[0] for k, row in zip(c, nonlinear_rows))
        if response > 0:
            strict += 1
            assert all(f[j] > 0 for j in derived_classes if j)
        if response > best:
            best, maximizers = response, [f]
        elif response == best:
            maximizers.append(f)
    optimal_indicator = tuple(2 * int(j != 0 and j in derived_classes)
                              for j in range(len(sizes)))
    assert best == Fraction(1, group_order)
    assert optimal_indicator in maximizers
    assert all(all(f[j] == 2 for j in derived_classes if j)
               for f in maximizers)
    print(f"{name}: admissible={checked}, strict={strict}, optimum={best}, "
          f"maximizers={len(maximizers)}")


def is_prime(n):
    return n >= 2 and all(n % k for k in range(2, isqrt(n) + 1))


def check_primes(limit):
    event = []
    for p in range(3, limit + 1):
        if p % 8 != 1 or not is_prime(p):
            continue
        euler_test = pow(2, (p - 1) // 4, p) == p - 1
        no_root = all(pow(x, 4, p) != 2 for x in range(1, p))
        assert euler_test == no_root
        if no_root:
            event.append(p)
    assert event[:5] == [17, 41, 97, 137, 193]
    print(f"Quartic test through {limit}: {len(event)} selected primes, "
          f"first ten={event[:10]}")


if __name__ == "__main__":
    # S3: identity, transpositions, 3-cycles.
    check_group("S3", [1, 3, 2], [0, 2], [[2, 0, -1]])
    # A4: identity, double transpositions, two inverse classes of 3-cycles.
    check_group("A4", [1, 3, 4, 4], [0, 1], [[3, -1, 0, 0]], [(2, 3)])
    # D4 of order 8: identity, half-turn, quarter-turns, two reflection classes.
    check_group("D4", [1, 1, 2, 2, 2], [0, 1], [[2, -2, 0, 0, 0]])
    # S4: identity, transpositions, double transpositions, 3-cycles, 4-cycles.
    check_group("S4", [1, 6, 3, 8, 6], [0, 2, 3],
                [[2, 0, 2, -1, 0], [3, 1, -1, 0, -1], [3, -1, -1, 0, 1]])
    check_primes(5000)
