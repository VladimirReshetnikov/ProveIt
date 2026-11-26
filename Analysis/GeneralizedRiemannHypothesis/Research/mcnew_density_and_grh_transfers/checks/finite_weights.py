"""Exact maximum-weight threshold verification for rational geometric triples."""
from math import prod


def reciprocal_sum(values):
    from fractions import Fraction
    return sum((Fraction(1, n) for n in values), Fraction())


def smooth_through(primes, limit):
    values = [1]
    for prime in primes:
        current = []
        for base in values:
            value = base
            while value <= limit:
                current.append(value)
                value *= prime
        values = current
    return sorted(values)


def verify_threshold(values, weights, threshold):
    """Return visited node count, raising if any admissible weight exceeds threshold."""
    assert values == sorted(set(values)) and min(values) > 0
    assert len(weights) == len(values) and all(type(w) is int and w > 0 for w in weights)
    indices = {value: index for index, value in enumerate(values)}
    implications = [[] for _ in values]
    for middle_index, middle in enumerate(values):
        for first_index in range(middle_index):
            last, remainder = divmod(middle * middle, values[first_index])
            if remainder == 0 and last in indices:
                implications[middle_index].append((1 << first_index, 1 << indices[last]))

    visits = 0

    def visit(remaining, chosen, bound):
        nonlocal visits
        visits += 1
        if bound <= threshold:
            return
        if remaining == 0:
            raise AssertionError("Admissible subset exceeds certified bound")
        bit = remaining & -remaining
        index = bit.bit_length() - 1
        remaining ^= bit
        visit(remaining, chosen, bound - weights[index])
        forbidden = 0
        for first, last in implications[index]:
            if chosen & first:
                forbidden |= last
        forbidden &= remaining
        remaining ^= forbidden
        while forbidden:
            last = forbidden & -forbidden
            bound -= weights[last.bit_length() - 1]
            forbidden ^= last
        visit(remaining, chosen | bit, bound)

    visit((1 << len(values)) - 1, 0, sum(weights))
    return visits
