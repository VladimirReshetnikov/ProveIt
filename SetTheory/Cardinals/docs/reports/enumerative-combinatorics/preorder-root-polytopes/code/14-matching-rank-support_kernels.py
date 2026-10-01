"""Exact matching-support kernels; Python 3.10+, standard library only.

Counts vertex supports, NOT perfect matchings. The algorithms deliberately use
small transparent matching routines. The arithmetic is exact throughout.
"""
from __future__ import annotations
from collections import Counter
from functools import lru_cache
from itertools import product
from math import comb
from random import Random
from typing import Iterable, Iterator, Sequence


def trim(p: Sequence[int]) -> list[int]:
    out = list(p)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


@lru_cache(maxsize=100000)
def perfectly_matchable(rows: tuple[int, ...]) -> bool:
    """Each row is a bit mask of neighbors on the opposite shore.

    Callers supply exactly len(rows) columns. This decision routine never
    counts matchings and thus cannot introduce multiplicity into a support.
    """
    if not rows:
        return True
    row = min(rows, key=int.bit_count)
    if not row:
        return False
    rest = list(rows)
    rest.remove(row)
    while row:
        bit = row & -row
        row -= bit
        if perfectly_matchable(tuple(r & ~bit for r in rest)):
            return True
    return False


def validate_bipartite(rows: Sequence[int], n_right: int) -> None:
    if n_right < 0 or any(not isinstance(r, int) or r < 0 or r >> n_right
                          for r in rows):
        raise ValueError('Invalid right-shore size or neighbor bit mask.')


def minimum_bipartite_cover(rows: Sequence[int], n_right: int
                            ) -> tuple[list[int], list[int]]:
    """Kuhn augmentations, followed by the alternating-path Konig cover."""
    validate_bipartite(rows, n_right)
    owner = [-1] * n_right
    def augment(u: int, seen: set[int]) -> bool:
        for v in range(n_right):
            if rows[u] >> v & 1 and v not in seen:
                seen.add(v)
                if owner[v] == -1 or augment(owner[v], seen):
                    owner[v] = u
                    return True
        return False
    for u in range(len(rows)):
        augment(u, set())
    mate = {u: v for v, u in enumerate(owner) if u >= 0}
    left_seen = set(range(len(rows))) - set(mate)
    right_seen: set[int] = set()
    pending = list(left_seen)
    while pending:
        u = pending.pop()
        for v in range(n_right):
            if rows[u] >> v & 1 and mate.get(u) != v and v not in right_seen:
                right_seen.add(v)
                if owner[v] >= 0 and owner[v] not in left_seen:
                    left_seen.add(owner[v])
                    pending.append(owner[v])
    return sorted(set(range(len(rows))) - left_seen), sorted(right_seen)


def quota_vectors(capacities: Sequence[int], budget: int
                  ) -> Iterator[tuple[int, ...]]:
    """All nonnegative quotas bounded coordinatewise, with total <= budget."""
    if budget < 0 or any(n < 0 for n in capacities):
        raise ValueError('Capacities and budget must be nonnegative.')
    def rec(i: int, remaining: int, prefix: tuple[int, ...]):
        if i == len(capacities):
            yield prefix
        else:
            for q in range(min(capacities[i], remaining) + 1):
                yield from rec(i + 1, remaining - q, prefix + (q,))
    yield from rec(0, budget, ())


@lru_cache(maxsize=256)
def bipartite_kernel_table(a: int, b: int, core: int
                          ) -> tuple[tuple[tuple[int, ...], ...],
                                     tuple[tuple[int, ...], ...],
                                     tuple[tuple[int, int, int, int], ...]]:
    """Finite table independent of all exterior population sizes.

    a left and b right vertices constitute the cover. core has a*b bits.
    Exterior left types are nonempty subsets of the b cover vertices;
    exterior right types are nonempty subsets of the a cover vertices.
    Returned entries (i,j,k,m) mean m cover selections produce a feasible
    k-support for exterior quota vectors i and j.
    """
    if a < 0 or b < 0 or core < 0 or core >> (a*b):
        raise ValueError('Invalid kernel parameters.')
    ql = tuple(quota_vectors([b] * ((1 << b) - 1), b))
    qr = tuple(quota_vectors([a] * ((1 << a) - 1), a))
    terms: Counter[tuple[int, int, int]] = Counter()
    for lm in range(1 << a):
        left_cover = [i for i in range(a) if lm >> i & 1]
        for rm in range(1 << b):
            right_cover = [j for j in range(b) if rm >> j & 1]
            for qi, lq in enumerate(ql):
                le = [t for t, q in enumerate(lq, 1) for _ in range(q)]
                k = len(left_cover) + len(le)
                for qj, rq in enumerate(qr):
                    if k != len(right_cover) + sum(rq):
                        continue
                    re = [t for t, q in enumerate(rq, 1) for _ in range(q)]
                    rows = []
                    for i in left_cover:
                        row = sum(1 << j for j, old in enumerate(right_cover)
                                  if core >> (i*b + old) & 1)
                        row |= sum(1 << (len(right_cover) + j)
                                   for j, t in enumerate(re) if t >> i & 1)
                        rows.append(row)
                    rows.extend(sum(1 << j for j, old in enumerate(right_cover)
                                    if t >> old & 1) for t in le)
                    if perfectly_matchable(tuple(rows)):
                        terms[qi, qj, k] += 1
    return ql, qr, tuple((i, j, k, m) for (i, j, k), m in terms.items())


def bipartite_population_counts(a: int, b: int, core: int,
                                left_pop: Sequence[int],
                                right_pop: Sequence[int]) -> list[int]:
    """Counts from a cover and binary-encodable exterior populations."""
    if len(left_pop) != (1 << b) - 1 or len(right_pop) != (1 << a) - 1:
        raise ValueError('Population array has the wrong number of types.')
    if any(not isinstance(n, int) or n < 0 for n in (*left_pop, *right_pop)):
        raise ValueError('Populations must be nonnegative integers.')
    ql, qr, terms = bipartite_kernel_table(a, b, core)
    def weights(quotas, populations):
        out = []
        for q in quotas:
            v = 1
            for n, k in zip(populations, q):
                v *= comb(n, k) if k <= n else 0
            out.append(v)
        return out
    wl, wr = weights(ql, left_pop), weights(qr, right_pop)
    p = [0] * (a + b + 1)
    for i, j, k, m in terms:
        p[k] += m * wl[i] * wr[j]
    return trim(p)


def bipartite_counts(rows: Sequence[int], n_right: int) -> list[int]:
    """Exact support polynomial using a minimum vertex-cover kernel."""
    left, right = minimum_bipartite_cover(rows, n_right)
    a, b = len(left), len(right)
    ls, rs = set(left), set(right)
    core = sum(1 << (i*b+j) for i, u in enumerate(left)
               for j, v in enumerate(right) if rows[u] >> v & 1)
    lp, rp = [0] * ((1 << b) - 1), [0] * ((1 << a) - 1)
    for u in range(len(rows)):
        if u not in ls:
            mask = sum(1 << j for j, v in enumerate(right) if rows[u] >> v & 1)
            if mask:
                lp[mask-1] += 1
    for v in range(n_right):
        if v not in rs:
            mask = sum(1 << i for i, u in enumerate(left) if rows[u] >> v & 1)
            if mask:
                rp[mask-1] += 1
    return bipartite_population_counts(a, b, core, lp, rp)


def maximal_matching_cover(n: int, arcs: set[tuple[int, int]]) -> list[int]:
    """Endpoints of a greedy maximal matching in the undirected shadow."""
    cover: set[int] = set()
    for u, v in sorted({tuple(sorted((u, v))) for u, v in arcs if u != v}):
        if u not in cover and v not in cover:
            cover.update((u, v))
    return sorted(cover)


def relation_macrostates(n: int, arcs: Iterable[tuple[int, int]]):
    """Yield feasible directed disjoint-support macrostates and their weights.

    Output: (size, multiplicity, cover_A, cover_B, [(type_members,p,q),...]).
    Loops are discarded: A and B are disjoint by definition.
    """
    edges = {(u, v) for u, v in arcs if u != v}
    if n < 0 or any(not (0 <= u < n and 0 <= v < n) for u, v in edges):
        raise ValueError('Relation endpoints are outside the vertex set.')
    cover = maximal_matching_cover(n, edges)
    c, cs = len(cover), set(cover)
    types: dict[tuple[int, int], list[int]] = {}
    for v in range(n):
        if v in cs:
            continue
        incoming = sum(1 << i for i, u in enumerate(cover) if (u, v) in edges)
        outgoing = sum(1 << i for i, u in enumerate(cover) if (v, u) in edges)
        if incoming or outgoing:
            types.setdefault((incoming, outgoing), []).append(v)
    members = list(types.values())
    quotas = []
    def build_q(i, remaining, acc, multiplicity):
        if i == len(members):
            quotas.append((tuple(acc), multiplicity))
            return
        pop = len(members[i])
        for p in range(min(pop, remaining) + 1):
            for q in range(min(pop-p, remaining-p) + 1):
                build_q(i+1, remaining-p-q, acc+[(p, q)],
                        multiplicity * comb(pop, p) * comb(pop-p, q))
    build_q(0, c, [], 1)
    for status in product(range(3), repeat=c):
        ca = tuple(u for u, s in zip(cover, status) if s == 1)
        cb = tuple(u for u, s in zip(cover, status) if s == 2)
        for qs, mult in quotas:
            aa, bb = list(ca), list(cb)
            for vs, (p, q) in zip(members, qs):
                aa.extend(vs[:p])
                bb.extend(vs[p:p+q])
            if len(aa) != len(bb):
                continue
            rows = tuple(sum(1 << j for j, v in enumerate(bb) if (u, v) in edges)
                         for u in aa)
            if perfectly_matchable(rows):
                yield (len(aa), mult, ca, cb,
                       tuple((tuple(vs), p, q) for vs, (p, q) in zip(members, qs)))


def relation_counts(n: int, arcs: Iterable[tuple[int, int]]) -> list[int]:
    """Gamma-support coefficients for any loopless directed relation."""
    out = [0] * (n // 2 + 1)
    for k, weight, *_ in relation_macrostates(n, arcs):
        out[k] += weight
    return trim(out)


def sample_relation_support(n: int, arcs: Iterable[tuple[int, int]],
                            rng: Random, k: int | None = None
                            ) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Uniform support pair, optionally conditioned on size, without rejection.

    Random.randrange/sample implement exact finite choices using integer
    arithmetic; the quality of the underlying random generator is separate.
    """
    states = [s for s in relation_macrostates(n, arcs) if k is None or s[0] == k]
    total = sum(s[1] for s in states)
    if total == 0:
        raise ValueError('No support of the requested size.')
    ticket = rng.randrange(total)
    for _, weight, ca, cb, types in states:
        if ticket >= weight:
            ticket -= weight
            continue
        aa, bb = list(ca), list(cb)
        for members, p, q in types:
            chosen = rng.sample(members, p + q)
            aa.extend(chosen[:p])
            bb.extend(chosen[p:])
        return tuple(sorted(aa)), tuple(sorted(bb))
    raise AssertionError('Unreachable cumulative-sampling branch.')


def rank_three_counts(x: int, y: int, z: int, w: int,
                      alpha: int, beta: int) -> list[int]:
    if any(v < 0 for v in (x, y, z, w)) or alpha not in (0, 1) or beta not in (0, 1):
        raise ValueError('Nonnegative populations and Boolean core edges required.')
    A = x+y+2*z
    B = x*y+x*z+y*z+comb(z, 2)
    C = alpha*(y+z)+beta*(x+z)-alpha*beta*z
    return trim([1, w+A+alpha+beta, w*A+B+C, w*B])


def rank_four_family_counts(N: int) -> list[int]:
    if N < 1:
        raise ValueError('This family is stated for N >= 1.')
    return [1, 8*N+4, 23*N*N+11*N+1, 28*N**3+5*N*N,
            N*N*(7*N-1)**2//4]


def rank_ulc_gaps(p: Sequence[int]) -> list[int]:
    p = trim(p)
    r = len(p)-1
    return [k*(r-k)*p[k]**2-(k+1)*(r-k+1)*p[k-1]*p[k+1]
            for k in range(1, r)]
