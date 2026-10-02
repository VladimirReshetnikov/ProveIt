#!/usr/bin/env python3
"""Exact finite consistency checks for the two rank bounds and barrier family.

Run with Python 3.10+ and its standard library. No finite check is asserted to
prove the all-size rank theorems. The script does not compute exact ranks.
"""
from fractions import Fraction
from math import gcd
import json
from check_templates import check_templates


def image(subset, rows):
    result = 0
    while subset:
        bit = subset & -subset
        subset -= bit
        result |= rows[bit.bit_length() - 1]
    return result


def transpose(rows):
    n = len(rows)
    return [sum(1 << i for i in range(n) if rows[i] & (1 << j))
            for j in range(n)]


def total_core(relations):
    subset = (1 << len(relations[0])) - 1
    while True:
        new = sum(1 << i for i in range(len(relations[0]))
                  if subset & (1 << i)
                  and all(rows[i] & subset for rows in relations))
        if new == subset:
            return subset
        subset = new


def barrier(n):
    relations = [[0] * n for _ in range(2)]
    edges = [(i, (i - 1) % n,
              (0,) if i in (0, 1) else (1,) if i == n - 1 else (0, 1))
             for i in range(n)]
    edges += [(0, n - 3, (0, 1)), (2, n - 1, (0, 1))]
    for start, end, labels in edges:
        for letter in labels:
            relations[letter][start] |= 1 << end
    q = (1 << n) - 1
    a, c = q ^ (1 << (n - 2)), q ^ 1
    for subset in (q, a, c):
        assert image(subset, relations[0]) == a
        assert image(subset, relations[1]) == c
    assert total_core(relations) == 0
    assert total_core([transpose(rows) for rows in relations]) == 0
    underlying = [relations[0][i] | relations[1][i] for i in range(n)]
    power = [1 << i for i in range(n)]
    exponent = (n - 1) * (n - 2)
    girth = None
    for length in range(1, exponent + 1):
        power = [image(row, underlying) for row in power]
        if girth is None and any(row & (1 << i) for i, row in enumerate(power)):
            girth = length
        assert all(row == q for row in power) == (length == exponent)
    assert girth == n - 2
    reverse = transpose(underlying)
    suffix_lengths = []
    for final in range(n):
        predecessors = 1 << final
        for length in range(1, n - 1):
            predecessors = image(predecessors, reverse)
            if predecessors.bit_count() >= 2:
                suffix_lengths.append(length)
                break
        else:
            raise AssertionError((n, final, 'no two-state suffix layer'))
    return {'n': n, 'boolean_exponent': exponent, 'girth': girth,
            'largest_first_branch_suffix_length': max(suffix_lengths),
            'three_subset_certificate': True,
            'forward_total_core_empty': True, 'backward_total_core_empty': True}


def arithmetic(maximum_n):
    hamiltonian = near = 0
    for n in range(4, maximum_n + 1):
        for j in range(n // 2 + 1, n):
            if gcd(n, j) != 1:
                continue
            k = n - j
            for a in range(1, k + 2):
                exponent = n - a + 1 + (n - 2) * j
                c = j - a
                assert c >= 0
                if c == 0:
                    assert n % 2 == 1 and j == a == (n + 1) // 2
                    assert 2 * exponent + 1 == n * n
                else:
                    mu = Fraction(n - j + a + 1, n)
                    bound = 2 * mu * (exponent - n + 1) + 2 * n + 1
                    assert 0 <= mu <= 1 and bound <= n * n + n + 1
                    derivative_at_endpoint = (n + 1) * j - 3 * n - 1
                    assert derivative_at_endpoint >= 0
                    assert (n - j) * (c - 1) >= 0
                hamiltonian += 1
        if n >= 6:
            for j in range((n + 1) // 2, n - 1):
                if gcd(n - 1, j) != 1:
                    continue
                e_upper = n + j * (n - 3)
                c = 2 * j - n
                if 2 * j == n:
                    assert 2 * e_upper + 1 == n * n - n + 1
                elif c <= 4:
                    assert 2 * e_upper + 1 <= n * n + 3 * n - 11
                else:
                    mu = Fraction(2 * n - 2 * j + 3, n - 1)
                    bound = 2 * mu * (e_upper - n + 1) + 2 * n + 1
                    assert 0 <= mu <= 1 and bound <= n * n + 3 * n - 9
                    assert (n - 3) * (2 * n + 3 - 4 * j) - 2 < 0
                near += 1
        assert (n - 1) ** 2 + 4 <= n * n + n + 1
        if n % 2:
            assert n * n - n + 3 <= n * n + n + 1
    for n in range(2, 6):
        assert 2 * (n - 1) ** 2 + 3 <= n * n + 3 * n
    return {'maximum_n': maximum_n, 'hamiltonian_parameter_triples': hamiltonian,
            'near_hamiltonian_parameter_pairs': near, 'all_checks_passed': True}


def main():
    result = {
        'scope': 'Finite consistency checks only; no all-size proof or exact rank computation',
        'arithmetic': arithmetic(150),
        'near_hamiltonian_full_templates': check_templates(20),
        'near_wielandt_instances': [barrier(n) for n in range(5, 22, 2)],
        'all_checks_passed': True,
    }
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
