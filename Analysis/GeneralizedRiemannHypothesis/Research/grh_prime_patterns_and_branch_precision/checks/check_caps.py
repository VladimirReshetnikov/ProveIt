"""Check the two-deletion theorem directly in small ternary affine spaces."""
from fractions import Fraction
from itertools import combinations, product
from math import prod


def third(x, y):
    return tuple((-a-b) % 3 for a, b in zip(x, y))


def max_added_mass(old, possible, weights):
    """Exhaust all caps extending old by candidates; no structural rules used."""
    best = 0
    def search(chosen, rest, score):
        nonlocal best
        best = max(best, score)
        if not rest or score + sum(weights[x] for x in rest) <= best:
            return
        x = rest[-1]
        rest = rest[:-1]
        search(chosen, rest, score)
        excluded = {third(x, y) for y in chosen}
        search(chosen + [x], [y for y in rest if y not in excluded], score + weights[x])
    search(list(old), list(possible), 0)
    return best


def verify(w):
    n = len(w)
    cube = set(product(range(2), repeat=n))
    outside = set(product(range(3), repeat=n)) - cube
    weights = {x: prod(a**d for a, d in zip(w, x)) for x in cube | outside}
    cases = 0
    for count in range(3):
        for dropped in combinations(sorted(cube), count):
            kept = cube.difference(dropped)
            secants = {third(x, y) for x, y in combinations(kept, 2)}
            optimum = max_added_mass(kept, sorted(outside - secants), weights)
            if count == 2:
                x, y = dropped
                changed = [i for i in range(n) if x[i] != y[i]]
                if len(changed) == 1:
                    m = changed[0]
                    base = prod(w[i]**x[i] for i in range(n) if i != m)
                    u = [w[i]**(2-x[i]) for i in range(n) if i != m]
                    expected = base * max(w[m]**2*(1+sum(u)),
                                          (1+w[m])*max(u, default=0))
                    assert optimum == expected, (w, dropped, optimum, expected)
                    cases += 1
                    continue
            assert optimum <= sum(weights[x] for x in dropped)
            cases += 1
    return cases


if __name__ == '__main__':
    weights = tuple(Fraction(1, p) for p in (2, 3, 5, 7))
    count = sum(verify(weights[:n]) for n in range(1, 5))
    count += sum(verify((Fraction(1,2),)*n) for n in range(1, 5))
    print(f"All {count} small weighted cube instances agree with the proof.")
    w = Fraction(1, 2)
    for k in (9, 10, 11):
        change = w**k * (w*w*(1+k*w) - (1+w))
        print(f"{k} satellites of weight 1/2: unnormalized change {change}")
