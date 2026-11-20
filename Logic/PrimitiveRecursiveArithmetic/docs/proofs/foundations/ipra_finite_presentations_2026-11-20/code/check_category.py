"""Exact finite examples for CategoryCase and SheafCase; Python standard library."""
from dataclasses import dataclass
from itertools import product
import json


def subset(small, large):
    return small & large == small


def topologies(d):
    num_masks = 1 << d
    for family in range(1 << num_masks):
        opens = tuple(u for u in range(num_masks) if family >> u & 1)
        if (0 in opens and num_masks - 1 in opens
                and all((u & v) in opens and (u | v) in opens for u in opens for v in opens)):
            yield opens


def points(u):
    return tuple(i for i in range(u.bit_length()) if u >> i & 1)


def basic_opens(opens):
    full = max(opens)
    result = {}
    for x in points(full):
        n = full
        for u in opens:
            if u >> x & 1:
                n &= u
        result[x] = n
    return result


@dataclass
class Presheaf:
    # sections[u] holds different, hashable sections; restrictions are exact tables.
    sections: dict
    restrictions: dict

    def res(self, u, v, a):
        return self.restrictions[u, v, a]


def triples(opens):
    return ((u, v) for u in opens for v in opens if subset(v, u))


def constant(opens, size):
    sections = {u: tuple(range(size)) for u in opens}
    return Presheaf(sections, {(u, v, a): a for u, v in triples(opens) for a in sections[u]})


def function_sheaf(opens):
    sections = {u: tuple(product((0, 1), repeat=len(points(u)))) for u in opens}
    restrictions = {}
    for u, v in triples(opens):
        for a in sections[u]:
            by_point = dict(zip(points(u), a))
            restrictions[u, v, a] = tuple(by_point[x] for x in points(v))
    return Presheaf(sections, restrictions)


def reflect(opens, f):
    ns = basic_opens(opens)
    sections = {}
    for u in opens:
        coords = points(u)
        result = []
        for a in product(*(f.sections[ns[x]] for x in coords)):
            by_point = dict(zip(coords, a))
            if all(f.res(ns[x], ns[y], by_point[x]) == by_point[y]
                   for x in coords for y in points(ns[x])):
                result.append(a)
        sections[u] = tuple(result)
    restrictions = {}
    for u, v in triples(opens):
        for a in sections[u]:
            by_point = dict(zip(points(u), a))
            restrictions[u, v, a] = tuple(by_point[y] for y in points(v))
    reflected = Presheaf(sections, restrictions)
    unit = {(u, a): tuple(f.res(u, ns[x], a) for x in points(u))
            for u in opens for a in f.sections[u]}
    return reflected, unit


def homs(opens, f, g):
    slots = [(u, a) for u in opens for a in f.sections[u]]
    for values in product(*(g.sections[u] for u, _ in slots)):
        h = dict(zip(slots, values))
        if all(g.res(u, v, h[u, a]) == h[v, f.res(u, v, a)]
               for u, v in triples(opens) for a in f.sections[u]):
            yield h


def extend(opens, sf, g, h):
    ns = basic_opens(opens)
    result = {}
    for u in opens:
        for a in sf.sections[u]:
            candidates = [t for t in g.sections[u]
                          if all(g.res(u, ns[x], t) == h[ns[x], ax]
                                 for x, ax in zip(points(u), a))]
            assert len(candidates) == 1
            result[u, a] = candidates[0]
    return result


def check_reflection():
    counts = dict(topologies=0, presheaves=0, inverse_pairs=0)
    for d in range(3):
        for opens in topologies(d):
            counts["topologies"] += 1
            g = function_sheaf(opens)
            for size in (0, 1, 2):
                f = constant(opens, size)
                sf, unit = reflect(opens, f)
                source = list(homs(opens, f, g))
                target = list(homs(opens, sf, g))
                for h in source:
                    k = extend(opens, sf, g, h)
                    assert k in target
                    assert {key: k[key[0], val] for key, val in unit.items()} == h
                for k in target:
                    h = {key: k[key[0], val] for key, val in unit.items()}
                    assert h in source and extend(opens, sf, g, h) == k
                assert len(source) == len(target)
                counts["presheaves"] += 1
                counts["inverse_pairs"] += len(target)
    return counts


def check_towers():
    counts = dict(towers=0, rates=0, valid_rates=0, coherent_edges=0)
    # Three arbitrary bonds on {0,1}, then identity forever.
    maps = tuple(product((0, 1), repeat=2))
    for bonds in product(maps, repeat=3):
        counts["towers"] += 1

        def proj(n, m, z):
            for j in reversed(range(n, min(3, m))):
                z = bonds[j][z]
            return z

        def image(n, m):
            return {proj(n, m, z) for z in (0, 1)}

        for guesses in product(*(range(n, 5) for n in range(4))):
            def s(n):
                return guesses[n] if n < 4 else n

            def cap(n):
                return max(s(n), s(n + 1))

            counts["rates"] += 1
            local = all(image(n, s(n)) <= image(n, cap(n)) for n in range(4))
            stable = all(image(n, s(n)) == image(n, t)
                         for n in range(4) for t in range(s(n), 5))
            assert local == stable
            if local:
                counts["valid_rates"] += 1
                for n in range(4):
                    for a in image(n, s(n)):
                        prev = a
                        for level in range(n, 8):
                            z = next(z for z in (0, 1) if proj(level, cap(level), z) == prev)
                            child = proj(level + 1, cap(level), z)
                            assert child in image(level + 1, s(level + 1))
                            assert proj(level, level + 1, child) == prev
                            assert proj(n, level + 1, child) == a
                            counts["coherent_edges"] += 1
                            prev = child
    return counts


if __name__ == "__main__":
    print(json.dumps({"sheafification": check_reflection(), "stable_images": check_towers()},
                     indent=2, sort_keys=True))
