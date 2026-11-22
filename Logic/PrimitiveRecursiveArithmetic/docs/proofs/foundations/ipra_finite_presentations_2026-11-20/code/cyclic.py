"""Positive rule tables. A row is (head, prerequisite mask, port mask)."""
from itertools import combinations, product


def subset(small, big):
    return small & big == small


def closure(vertices, rules, ports):
    """Return the closure, first-entry ranks, and the first producing rule."""
    known = 0
    ranks = [0] * vertices
    producers = [-1] * vertices
    for step in range(1, vertices + 1):
        new = known
        for index, (head, needs, guards) in enumerate(rules):
            if subset(needs, known) and subset(guards, ports):
                if not new & (1 << head):
                    ranks[head] = step
                    producers[head] = index
                new |= 1 << head
        if new == known:
            break
        known = new
    return known, ranks, producers


def check_certificate(vertices, rules, ports, cert):
    known, ranks, producers = cert
    if known >= 1 << vertices or len(ranks) != vertices or len(producers) != vertices:
        return False
    for v in range(vertices):
        if known >> v & 1:
            i = producers[v]
            if not (1 <= ranks[v] <= vertices and 0 <= i < len(rules)):
                return False
            head, needs, guards = rules[i]
            if head != v or not subset(guards, ports) or not subset(needs, known):
                return False
            if any(ranks[w] >= ranks[v] for w in range(vertices) if needs >> w & 1):
                return False
    return all(not (subset(n, known) and subset(g, ports)) or known >> h & 1
               for h, n, g in rules)


def minimal_supports(vertices, port_count, rules, target):
    good = []
    for mask in range(1 << port_count):
        if closure(vertices, rules, mask)[0] >> target & 1:
            if not any(subset(s, mask) for s in good):
                good.append(mask)
    return good


def eliminate_second_vertex(rules, ports):
    """Eliminate vertex 1 while retaining feedback from vertex 0."""
    def inner(x):
        # x supplies external vertex 0 to the inner one-vertex system.
        return any(h == 1 and subset(g, ports) and subset(n, x)
                   for h, n, g in rules)
    y0 = 2 if inner(0) else 0
    x = int(any(h == 0 and subset(g, ports) and subset(n, y0)
                for h, n, g in rules))
    return x | (2 if inner(x) else 0)


def self_check():
    # Independent least-closed-set semantics runs through every subset.
    v, p = 2, 2
    pool = list(product(range(v), range(1 << v), range(1 << p)))
    count = 0
    for size in range(4):
        for rules in combinations(pool, size):
            answers = []
            for supplied in range(1 << p):
                cert = closure(v, rules, supplied)
                assert check_certificate(v, rules, supplied, cert)
                closed = [s for s in range(1 << v) if all(
                    not (subset(n, s) and subset(g, supplied)) or s >> h & 1
                    for h, n, g in rules)]
                intersection = (1 << v) - 1
                for s in closed:
                    intersection &= s
                assert cert[0] == intersection == eliminate_second_vertex(rules, supplied)
                answers.append(intersection)
                count += 1
            for goal in range(v):
                supports = minimal_supports(v, p, rules, goal)
                for supplied, ans in enumerate(answers):
                    assert any(subset(s, supplied) for s in supports) == bool(ans >> goal & 1)
    example = [(0, 2, 0), (1, 1, 0), (0, 0, 3), (1, 0, 4)]
    assert minimal_supports(2, 3, example, 0) == [3, 4]
    assert not check_certificate(2, example, 0, (3, [1, 1], [0, 1]))
    print(f"cyclic: {count} table/port cases; both goals and all minimal supports checked")


if __name__ == "__main__":
    self_check()
