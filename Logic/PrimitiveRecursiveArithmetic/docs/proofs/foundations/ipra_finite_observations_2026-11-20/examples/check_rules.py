"""Independent brute-force checks for the small finite instances of the paper."""
from itertools import product
from random import Random

from finite_rules import Presentation, Rule, canonical, lift, sheet_example


def all_partitions(n):
    return sorted({canonical(c) for c in product(range(max(1, n)), repeat=n)})


def finer(p, q):
    return all(a != b or c == d for a, c in zip(p, q) for b, d in zip(p, q))


def check(p):
    partitions = all_partitions(p.size)
    closed = [m for m in range(p.full + 1) if p.step(m) == m]
    intersection = p.full
    for m in closed:
        intersection &= m
    assert p.saturate()[0] == intersection
    for a in range(p.size):
        ev = p.evidence(a)
        assert p.verify(a, ev) and ((ev[0] == "proof") == bool(intersection >> a & 1))
    stable = []
    for c in partitions:
        masks = {lift(c, x) for x in range(1 << (max(c, default=-1) + 1))}
        if all(p.step(x) in masks for x in masks):
            stable.append(c)
            q = p.quotient(c)
            for x in range(q.full + 1):
                assert lift(c, q.step(x)) == p.step(lift(c, x))
    for c in partitions:
        got = p.refinement(c)
        assert got in stable and finer(got, c)
        assert all(finer(d, got) for d in stable if finer(d, c))


def main():
    count = 0
    for n in range(3):
        rules = [Rule(h, b) for h in range(n) for b in range(1 << n)]
        for i in range(1 << len(rules)):
            check(Presentation(n, [r for j, r in enumerate(rules) if i >> j & 1]))
            count += 1
    rng = Random(901)
    for n in (3, 4):
        for _ in range(50):
            p = Presentation(n, [Rule(rng.randrange(n), rng.randrange(1 << n))
                                 for _ in range(rng.randrange(2 * n + 1))])
            check(p)
    for close in [False, True]:
        _, p = sheet_example(close)
        assert (p.evidence(1)[0] == 'proof') == close
        assert p.verify(1, p.evidence(1))
    print(f"Passed all {count} systems on 0–2 atoms, 100 seeded systems on 3–4 atoms, and two sheet examples.")


if __name__ == "__main__":
    main()
