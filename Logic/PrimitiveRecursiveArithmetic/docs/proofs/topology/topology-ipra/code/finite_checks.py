#!/usr/bin/env python3
"""Run with python3 code/finite_checks.py (standard library, no arguments).

Exhaust all labelled topologies on zero to four points and all pairs of
their isomorphism types. An independent search for homotopy inverses uses
components of the identity in spaces of monotone maps, without core deletion.
The checks exercise the indicated finite instances of the general proofs.
"""

from functools import cache
from itertools import combinations, permutations, product


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def points(mask, n):
    return (x for x in range(n) if mask >> x & 1)


def open_sets(rows):
    n = len(rows)
    return tuple(a for a in range(1 << n)
                 if all(rows[x] & ~a == 0 for x in points(a, n)))


def from_opens(opens, n):
    whole = (1 << n) - 1
    rows = [whole] * n
    for a in opens:
        for x in points(a, n):
            rows[x] &= a
    return tuple(rows)


def all_topologies(n):
    whole = (1 << n) - 1
    optional = tuple(range(1, whole))
    for choice in range(1 << len(optional)):
        opens = {0, whole}
        opens.update(optional[i] for i in points(choice, len(optional)))
        if all((u & v) in opens and (u | v) in opens
               for u, v in combinations(opens, 2)):
            yield tuple(sorted(opens))


def all_preorders(n):
    edges = tuple((x, y) for x in range(n) for y in range(n) if x != y)
    for choice in range(1 << len(edges)):
        rows = [1 << x for x in range(n)]
        for k in points(choice, len(edges)):
            x, y = edges[k]
            rows[x] |= 1 << y
        if all(rows[y] & ~rows[x] == 0 for x in range(n)
               for y in points(rows[x], n)):
            yield tuple(rows)


def restrict(rows, labels):
    return tuple(sum(1 << j for j, y in enumerate(labels) if rows[x] >> y & 1)
                 for x in labels)


@cache
def canonical(rows):
    return min(restrict(rows, perm) for perm in permutations(range(len(rows))))


def components(rows):
    n = len(rows)
    seen = set()
    result = []
    for x in range(n):
        if x in seen:
            continue
        group = {x}
        frontier = [x]
        while frontier:
            u = frontier.pop()
            for v in range(n):
                if v not in group and (rows[u] >> v & 1 or rows[v] >> u & 1):
                    group.add(v)
                    frontier.append(v)
        result.append(sum(1 << y for y in group))
        seen.update(group)
    return tuple(result)


def check_open_algebra(rows, opens):
    n = len(rows)
    whole = (1 << n) - 1
    masks = range(whole + 1)
    closed = {whole ^ a for a in opens}
    dense = []
    for a in masks:
        interior = sum(1 << x for x in range(n) if rows[x] & ~a == 0)
        closure = sum(1 << x for x in range(n) if rows[x] & a)
        check(interior in opens and not (interior & ~a) and
              all(not (u & ~interior) for u in opens if u & ~a == 0),
              "interior maximum")
        check(closure in closed and not (a & ~closure) and
              all(not (closure & ~c) for c in closed if a & ~c == 0),
              "closure minimum")
        if closure == whole:
            dense.append(a)
    reps = [x for x in range(n) if rows[x] not in rows[:x]]
    maximal = [x for x in reps if all(rows[y] == rows[x]
               for y in points(rows[x], n))]
    check(min(a.bit_count() for a in dense) == len(maximal), "minimum density")
    check(all(any(rows[x] >> y & 1 and rows[y] >> x & 1
              for y in points(a, n)) for x in maximal for a in dense),
          "maximal classes meet every dense set")
    clopens = {a for a in opens if whole ^ a in opens}
    unions = {0}
    for comp in components(rows):
        unions |= {a | comp for a in unions}
    check(unions == clopens, "component unions equal clopens")

    irreducibles = {j for j in opens if j and all((a | b) != j
                    for a in opens if a != j for b in opens if b != j)}
    check(irreducibles == set(rows), "join-irreducible principal opens")
    for u, v in product(opens, repeat=2):
        implication = sum(1 << x for x in range(n) if rows[x] & u & ~v == 0)
        check(implication in opens and all((w & ~implication == 0) ==
              (w & u & ~v == 0) for w in opens), "Heyting adjunction")


def check_lattice_points(rows, opens):
    """Exhaust bounded lattice maps from the open algebra to {0 < 1}."""
    n = len(rows)
    index = {u: i for i, u in enumerate(opens)}
    lattice_edges = [(index[a], index[b], index[a & b], index[a | b])
                     for a, b in combinations(opens, 2)]
    characters = set()
    if len(opens) > 1:
        for middle in range(1 << (len(opens) - 2)):
            # A bounded homomorphism fixes the empty and full masks.
            code = (middle << 1) | (1 << (len(opens) - 1))
            bits = [(code >> i) & 1 for i in range(len(opens))]
            if all((bits[a] & bits[b]) == bits[meet] and
                   (bits[a] | bits[b]) == bits[join]
                   for a, b, meet, join in lattice_edges):
                characters.add(code)
    evaluations = {sum(1 << i for i, u in enumerate(opens) if u >> x & 1)
                   for x in range(n)}
    check(characters == evaluations, "lattice points equal evaluations")


def check_subspaces_and_quotients(rows, opens):
    n = len(rows)
    for subset in range(1 << n):
        labels = tuple(points(subset, n))
        relative = {sum(1 << i for i, x in enumerate(labels) if u >> x & 1)
                    for u in opens}
        check(relative == set(open_sets(restrict(rows, labels))), "subspace")
    for m in range(n + 1):
        for q in product(range(m), repeat=n):
            # Increasing first occurrences give each partition one labelling.
            if tuple(dict.fromkeys(q)) != tuple(range(m)):
                continue
            final_opens = {v for v in range(1 << m)
                           if sum(1 << x for x in range(n) if v >> q[x] & 1)
                           in opens}
            quotient = [1 << i for i in range(m)]
            for x in range(n):
                for y in points(rows[x], n):
                    quotient[q[x]] |= 1 << q[y]
            for k in range(m):
                for i in range(m):
                    if quotient[i] >> k & 1:
                        quotient[i] |= quotient[k]
            check(set(open_sets(quotient)) == final_opens, "quotient")


def check_covers(rows, opens):
    n = len(rows)
    whole = (1 << n) - 1
    reps = [x for x in range(n) if rows[x] not in rows[:x]]
    minimal = [x for x in reps if all(not (rows[y] >> x & 1)
               or rows[x] >> y & 1 for y in range(n))]
    principal = [rows[x] for x in minimal]
    check(all(not any(other >> x & 1 for other in principal if other != rows[x])
              for x in minimal), "each principal cover member indispensable")
    # Membership of the empty open has no effect on the cover or its witnesses.
    nonempty = tuple(u for u in opens if u)
    joins = [0] * (1 << len(nonempty))
    for family in range(1, len(joins)):
        bit = family & -family
        joins[family] = joins[family ^ bit] | nonempty[bit.bit_length() - 1]
    covers = 0
    for family, union in enumerate(joins):
        if union != whole:
            continue
        covers += 1
        extracted = 0
        for x in minimal:
            extracted |= next(nonempty[i] for i in points(family, len(nonempty))
                              if nonempty[i] >> x & 1)
        check(extracted == whole, "subcover at minimal representatives")
    check(covers > 0, "principal cover exists")
    return covers


@cache
def all_cores(rows):
    n = len(rows)
    # Equivalent points have exactly the same row in a preorder.
    reps = tuple(x for x in range(n) if rows[x] not in rows[:x])
    if len(reps) < n:
        return all_cores(restrict(rows, reps))
    survivors = set()
    for x in range(n):
        upper = [y for y in range(n) if x != y and rows[x] >> y & 1]
        lower = [y for y in range(n) if x != y and rows[y] >> x & 1]
        upbeat = any(all(rows[y] >> z & 1 for z in upper) for y in upper)
        downbeat = any(all(rows[z] >> y & 1 for z in lower) for y in lower)
        if upbeat or downbeat:
            labels = [y for y in range(n) if y != x]
            survivors.update(all_cores(restrict(rows, labels)))
    return frozenset(survivors or {canonical(rows)})


@cache
def monotone_maps(source, target):
    n = len(source)
    edges = tuple((x, y) for x in range(n) for y in points(source[x], n)
                  if x != y)
    return tuple(f for f in product(range(len(target)), repeat=n)
                 if all(target[f[x]] >> f[y] & 1 for x, y in edges))


@cache
def identity_component(rows):
    n = len(rows)
    identity = tuple(range(n))
    frontier = [identity]
    reached = {identity}
    unseen = set(monotone_maps(rows, rows)) - reached
    while frontier:
        f = frontier.pop()
        neighbours = {g for g in unseen if
                      all(rows[a] >> b & 1 for a, b in zip(f, g)) or
                      all(rows[b] >> a & 1 for a, b in zip(f, g))}
        frontier.extend(neighbours)
        reached.update(neighbours)
        unseen.difference_update(neighbours)
    return reached


def has_homotopy_inverses(x, y):
    idx = identity_component(x)
    idy = identity_component(y)
    for f in monotone_maps(x, y):
        for g in monotone_maps(y, x):
            if tuple(g[i] for i in f) in idx and tuple(f[i] for i in g) in idy:
                return True
    return False


def main():
    types = []
    covers = 0
    expected_labels = [1, 1, 4, 29, 355]
    expected_types = [1, 1, 3, 9, 33]
    for n in range(5):
        recovered = set()
        for opens in all_topologies(n):
            rows = from_opens(opens, n)
            check(open_sets(rows) == opens, "topology round trip")
            recovered.add(rows)
            check_open_algebra(rows, opens)
            check_lattice_points(rows, opens)
            check_subspaces_and_quotients(rows, opens)
            covers += check_covers(rows, opens)
            check(len(all_cores(rows)) == 1, "independence of deletion order")
        check(set(all_preorders(n)) == recovered, "preorder round trip")
        check(len(recovered) == expected_labels[n], "labelled count")
        representatives = sorted({canonical(rows) for rows in recovered})
        check(len(representatives) == expected_types[n], "isomorphism count")
        types.extend(representatives)
        print(f"{n} points: {len(recovered)} labelled, "
              f"{len(representatives)} isomorphism types")
    @cache
    def fixed_point_property(rows):
        return all(any(x == y for x, y in enumerate(f))
                   for f in monotone_maps(rows, rows))

    for x in types:
        if len(set(x)) == len(x):
            core = next(iter(all_cores(x)))
            check(fixed_point_property(x) == fixed_point_property(core),
                  "beat deletion preserves the fixed point property")
    pairs = 0
    for i, x in enumerate(types):
        for y in types[:i + 1]:
            equivalent = has_homotopy_inverses(x, y)
            check(equivalent == (all_cores(x) == all_cores(y)),
                  f"core classification for {x}, {y}")
            pairs += 1
    print(f"{covers} open covers (empty members suppressed)")
    print(f"{pairs} space-type pairs checked by independent homotopy-inverse search")
    print(f"{len({all_cores(x) for x in types})} distinct core types in total")


if __name__ == "__main__":
    main()
