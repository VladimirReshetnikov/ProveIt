"""Uniform finite category finality, a demonstrator for the proof in the paper.

An arrow index indexes src and tgt. comp[g,f] is g after f.
All externally supplied tables are assumed to satisfy the stated laws.
"""
from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class Cat:
    ids: tuple
    src: tuple
    tgt: tuple
    comp: dict

    def check(self):
        for a in range(len(self.ids)):
            i = self.ids[a]
            assert self.src[i] == self.tgt[i] == a
        for f, (a, b) in enumerate(zip(self.src, self.tgt)):
            assert self.comp[f, self.ids[a]] == self.comp[self.ids[b], f] == f
        for g, f in product(range(len(self.src)), repeat=2):
            if self.tgt[f] != self.src[g]:
                continue
            gf = self.comp[g, f]
            assert (self.src[gf], self.tgt[gf]) == (self.src[f], self.tgt[g])
            for h in range(len(self.src)):
                if self.src[h] == self.tgt[g]:
                    assert self.comp[h, gf] == self.comp[self.comp[h, g], f]


def components(n, edges):
    labels = list(range(n))
    for u, v in edges:
        to, old = labels[u], labels[v]
        labels = [to if val == old else val for val in labels]
    fixed = [i for i in range(n) if labels[i] == i]
    rank = {v: i for i, v in enumerate(fixed)}
    return [rank[v] for v in labels], fixed


def comma(J, K, on_obj, on_arr, d):
    vs = [(j, h) for j in range(len(J.ids)) for h in range(len(K.src))
          if (K.src[h], K.tgt[h]) == (d, on_obj[j])]
    idx = {v: i for i, v in enumerate(vs)}
    edges = [(i, idx[J.tgt[e], K.comp[on_arr[e], h]])
             for i, (j, h) in enumerate(vs)
             for e in range(len(J.src)) if J.src[e] == j]
    return vs, edges


def defects(J, K, on_obj, on_arr):
    bad = {}
    for d in range(len(K.ids)):
        vs, edges = comma(J, K, on_obj, on_arr, d)
        _, reps = components(len(vs), edges)
        if len(reps) != 1:
            bad[d] = [vs[i] for i in reps]
    return bad


def colimit(C, sizes, acts):
    vs = [(i, x) for i, n in enumerate(sizes) for x in range(n)]
    idx = {v: i for i, v in enumerate(vs)}
    edges = [(idx[i, x], idx[C.tgt[e], acts[e][x]]) for e, i in enumerate(C.src)
             for x in range(sizes[i])]
    labels, reps = components(len(vs), edges)
    return dict(zip(vs, labels)), [vs[r] for r in reps]


def compare(J, K, on_obj, on_arr, sizes, acts):
    target, out = colimit(K, sizes, acts)
    _, reps = colimit(J, [sizes[k] for k in on_obj], [acts[f] for f in on_arr])
    values = [target[on_obj[j], x] for j, x in reps]
    return sorted(values) == list(range(len(out)))


def small_diagrams(C, bound):
    for sizes in product(range(bound + 1), repeat=len(C.ids)):
        tables = [list(product(range(sizes[b]), repeat=sizes[a]))
                  for a, b in zip(C.src, C.tgt)]
        for i, e in enumerate(C.ids):
            tables[e] = [tuple(range(sizes[i]))]
        for acts in product(*tables):
            if all(acts[gf] == tuple(acts[g][y] for y in acts[f])
                   for (g, f), gf in C.comp.items()):
                yield sizes, acts


def examples():
    src, tgt = (0, 1, 0, 0, 1), (0, 1, 1, 1, 1)
    comp = {(f, (0, 1)[a]): f for f, a in enumerate(src)}
    comp.update({((0, 1)[b], f): f for f, b in enumerate(tgt)})
    comp.update({(4, 4): 1, (4, 2): 3, (4, 3): 2})
    K = Cat((0, 1), src, tgt, comp)
    group = Cat((0,), (0, 0), (0, 0), {(g, f): g ^ f for g, f in product(range(2), repeat=2)})
    point = Cat((0,), (0,), (0,), {(0, 0): 0})
    empty = Cat((), (), (), {})
    for C in (K, group, point, empty):
        C.check()
    tests = [
        ("full subgroupoid at t", group, K, (1,), (1, 4), True),
        ("identity only at t", point, K, (1,), (1,), False),
        ("identity only at s", point, K, (0,), (0,), False),
        ("empty to empty", empty, empty, (), (), True),
        ("empty to point", empty, point, (), (), False),
    ]
    for name, J, C, fo, fa, expected in tests:
        bad = defects(J, C, fo, fa)
        assert (not bad) == expected
        num = fails = 0
        for sizes, acts in small_diagrams(C, 2):
            num += 1
            fails += not compare(J, C, fo, fa, sizes, acts)
        assert (fails == 0) == expected
        for d in bad:
            hs = [[h for h in range(len(C.src)) if (C.src[h], C.tgt[h]) == (d, a)]
                  for a in range(len(C.ids))]
            acts = [[hs[C.tgt[f]].index(C.comp[f, h]) for h in hs[C.src[f]]]
                    for f in range(len(C.src))]
            assert not compare(J, C, fo, fa, list(map(len, hs)), acts)
        print(f"{name}: {num} diagrams (sizes <= 2), {fails} failed comparisons; defects {bad}")


if __name__ == "__main__":
    examples()
