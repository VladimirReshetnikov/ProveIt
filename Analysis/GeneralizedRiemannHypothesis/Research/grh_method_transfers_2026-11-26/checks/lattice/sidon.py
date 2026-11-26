"""Minimum group order for a five-element B_3 set; exhaustive finite check."""
from itertools import combinations_with_replacement, product
from math import isqrt


def invariant_factors(m, divisor=1):
    """Nontrivial factors in divisibility order, of product m."""
    yield (m,)
    for factor in range(max(divisor, 2), isqrt(m) + 1):
        if m % (factor * factor):
            continue
        if factor % divisor:
            continue
        for tail in invariant_factors(m // factor, factor):
            yield (factor, *tail)


def find_set(factors):
    points = list(product(*(range(q) for q in factors)))
    ids = {a: i for i, a in enumerate(points)}
    table = [[ids[tuple((x + y) % q for x, y, q in zip(a, b, factors))]
              for b in points] for a in points]

    def extend(chosen, double, triple):
        if len(chosen) == 5:
            return [points[i] for i in chosen]
        for x in range(chosen[-1] + 1, len(points)):
            # All new 3-sums contain x exactly once, twice, or three times.
            add_x = table[x]
            twice = add_x[x]
            new = {add_x[s] for s in double}
            new.update(table[twice][s] for s in chosen)
            new.add(add_x[twice])
            if len(new) != len(double) + len(chosen) + 1 or not triple.isdisjoint(new):
                continue
            next_double = double | {add_x[s] for s in chosen} | {twice}
            found = extend(chosen + [x], next_double, triple | new)
            if found is not None:
                return found
        return None
    return extend([0], {0}, {0})


if __name__ == '__main__':
    # The balanced anticode S_4(2,1) gives the elementary lower bound 55.
    for order in range(55, 64):
        for factors in invariant_factors(order):
            witness = find_set(factors)
            print(f'order={order} factors={factors} witness={witness}', flush=True)
            if witness is not None:
                raise AssertionError('Found a smaller group')
    for factors, should_exist in [((64,), False), ((8, 8), True), ((65,), True)]:
        witness = find_set(factors)
        print(f'factors={factors} witness={witness}', flush=True)
        if (witness is not None) != should_exist:
            raise AssertionError('Unexpected existence result')
        if witness:
            sums = {tuple(sum(coordinate) % q for coordinate, q in zip(zip(*triple), factors))
                    for triple in combinations_with_replacement(witness, 3)}
            if len(sums) != 35:
                raise AssertionError('Invalid witness')
