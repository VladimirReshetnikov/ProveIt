"""Compare sparse algorithms to independent, exhaustive full-word tables."""
from fractions import Fraction as F
from itertools import product
from random import Random
from sparse import (Ask, aggregates, carry_error, coherence_error, evaluate_name, evaluate_rational,
                    leaves, least_use, rational_bit, run, tent_tree)


def full_table(tree, width):
    return [run(tree, word.__getitem__) for word in product(range(2), repeat=width)]


def brute_use(values, width, error):
    for n in range(width + 1):
        block_size = 1 << (width - n)
        blocks = [values[i:i + block_size] for i in range(0, len(values), block_size)]
        if all(max(block) - min(block) <= error for block in blocks):
            return n


def random_tree(rng, depth, width):
    if depth == 0 or rng.randrange(5) == 0:
        return F(rng.randrange(-4, 6), rng.randrange(1, 4))
    return Ask(rng.randrange(width), random_tree(rng, depth-1, width),
               random_tree(rng, depth-1, width))


def check():
    rng = Random(93219)
    for _ in range(140):
        width = rng.randrange(1, 7)
        t, u = [random_tree(rng, 5, width) for _ in range(2)]
        rows = leaves(t)
        v, w = full_table(t, width), full_table(u, width)
        assert sum(F(1, 1 << len(row.answers)) for row in rows) == 1
        assert aggregates(rows) == (min(v), sum(v)/len(v), max(v))
        for eta in (0, F(1,3), 2, 10):
            assert least_use(rows, eta) == brute_use(v, width, eta)
        assert carry_error(rows) == max(abs(a-b) for a,b in zip(v, v[1:]))
        assert coherence_error(rows, leaves(u)) == max(abs(a-b) for a,b in zip(v,w))

    # Independent digit extraction against floor of a rational after a shift.
    for den in range(1, 13):
        for num in range(den+1):
            x = F(num,den)
            for q in range(20):
                expected = 1 if x == 1 else ((num << (q+1)) // den) % 2
                assert rational_bit(x, q) == expected
    inconsistent = Ask(7, Ask(7, 3, 500), Ask(7, -200, 3))
    assert aggregates(leaves(inconsistent)) == (3,3,3)
    assert least_use(leaves(inconsistent)) == 0
    assert carry_error(leaves(Ask(0,0,1))) == 1
    # A tiny number of terminal rows despite a very distant address.
    for offset in (0, 5, 10000):
        prev = None
        for m in range(1, 7):
            tree = tent_tree(offset,m)
            rows = leaves(tree)
            assert aggregates(rows)[1] == F(1,2)
            assert carry_error(rows) <= F(2, 1 << m)
            if prev:
                assert coherence_error(prev, rows) <= F(3, 1 << m)
            prev = rows
            if offset < 6:
                for i in range(50):
                    x = F(i,49)
                    phase = ((1 << offset)*x) % 1
                    exact = 2 * min(phase, 1-phase)
                    assert abs(evaluate_rational(tree, x) - exact) <= F(1, 1 << m)
        print(f"tent offset={offset}, digits=6, leaves={len(rows)}, "
              f"least exact prefix={least_use(rows)}, mean={aggregates(rows)[1]}")
    # Two interchangeable Cauchy names, including both sides of dyadic endpoints.
    # Reuse the finite trees. All comparisons below are exact rational bounds.
    trees = {k: tent_tree(3, max(1, k)) for k in range(8)}
    comparisons = 0
    for x in (F(0), F(1,16), F(1,2), F(7,17), F(1)):
        phase = (8*x) % 1
        exact = 2*min(phase,1-phase)
        outputs = []
        for sign in (-1,1):
            sample = lambda p: x + F(sign,1 << p)
            row = [evaluate_name(trees.__getitem__, sample, n) for n in range(4)]
            assert all(abs(y-exact) <= F(1,1<<n) for n,y in enumerate(row))
            outputs.append(row)
        for i,a in enumerate(outputs[0]):
            for j,b in enumerate(outputs[1]):
                assert abs(a-b) <= F(1,1<<i) + F(1,1<<j)
                comparisons += 1
    print(f"{comparisons} mixed-index Cauchy-name comparisons passed.")
    print("140 independent table comparisons passed for mass, extrema, mean, "
          "adjacency, coherence and four least-prefix tolerances. Digit and tent checks passed.")


if __name__ == "__main__":
    check()
