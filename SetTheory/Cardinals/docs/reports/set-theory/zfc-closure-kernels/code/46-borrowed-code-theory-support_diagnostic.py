#!/usr/bin/env python3
"""Finite diagnostics for the bounded-support interpretation obstruction.

These are exact finite group/term checks, not a finite model of EPSC1 and not
a proof of the infinite support theorem. No external package is required.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import combinations, permutations
import json
from pathlib import Path


@dataclass(frozen=True, order=True)
class Atom:
    index: int


def subsets(n: int, max_size: int | None = None):
    if max_size is None:
        max_size = n
    return [frozenset(c) for k in range(max_size + 1)
            for c in combinations(range(n), k)]


def compose(p, q):
    """Composition p after q, with permutations represented by image tuples."""
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p):
    out = [0] * len(p)
    for i, value in enumerate(p):
        out[value] = i
    return tuple(out)


def fixes(p, support):
    return all(p[i] == i for i in support)


def transpose(n, a, b):
    p = list(range(n))
    p[a], p[b] = b, a
    return tuple(p)


def extend_partial(n, partial, protected):
    """Extend a finite injective map disjoint from a protected set."""
    assert len(set(partial.values())) == len(partial)
    assert not (set(partial) & set(protected))
    assert not (set(partial.values()) & set(protected))
    out = dict(partial)
    out.update({i: i for i in protected})
    free_domain = sorted(set(range(n)) - set(out))
    free_range = sorted(set(range(n)) - set(out.values()))
    out.update(zip(free_domain, free_range))
    answer = tuple(out[i] for i in range(n))
    assert sorted(answer) == list(range(n))
    return answer


def stabilizer_factorization(n, f, h, g):
    """g=t^{-1} s r, with t,r fixing F and s fixing H."""
    c = f & h
    a = f - c
    b = h - c
    assert fixes(g, c)
    ga = {g[i] for i in a}
    bad = sorted(ga & b)
    fresh = sorted(set(range(n)) - (c | a | b | ga))
    assert len(fresh) >= len(bad), "Finite pool lacks the required fresh indices"
    t = tuple(range(n))
    for old, new in zip(bad, fresh):
        t = compose(transpose(n, old, new), t)
    assert fixes(t, f)
    assert not ({t[g[i]] for i in a} & b)
    s = extend_partial(n, {i: t[g[i]] for i in a}, b | c)
    r = compose(inverse(s), compose(t, g))
    assert fixes(s, h)
    assert fixes(r, f)
    assert compose(inverse(t), compose(s, r)) == g
    return t, s, r


def kuratowski(a, b):
    return frozenset((frozenset((a,)), frozenset((a, b))))


def tuple_code(items):
    assert items
    answer = items[-1]
    for item in reversed(items[:-1]):
        answer = kuratowski(item, answer)
    return answer


def act(term, p):
    if isinstance(term, Atom):
        return Atom(p[term.index])
    assert isinstance(term, frozenset)
    return frozenset(act(child, p) for child in term)


def supporting_subsets(term, ps, candidates):
    stabilizes = [act(term, p) == term for p in ps]
    return [f for f in candidates
            if all(not fixes(p, f) or stable
                   for p, stable in zip(ps, stabilizes))]


def run():
    n = 6
    ps = list(permutations(range(n)))
    small_supports = subsets(n, 2)
    decompositions = 0
    by_intersection = {}
    for f in small_supports:
        for h in small_supports:
            c = f & h
            for g in ps:
                if fixes(g, c):
                    stabilizer_factorization(n, f, h, g)
                    decompositions += 1
                    key = str(len(c))
                    by_intersection[key] = by_intersection.get(key, 0) + 1

    all_subsets = subsets(n)
    tuple_results = []
    stabilizer_comparisons = 0
    for k in range(1, 5):
        code = tuple_code([Atom(i) for i in range(k)])
        for p in ps:
            assert (act(code, p) == code) == fixes(p, range(k))
            stabilizer_comparisons += 1
        supports = supporting_subsets(code, ps, all_subsets)
        minimum = min(map(len, supports))
        minimal = [sorted(f) for f in supports if len(f) == minimum]
        assert minimum == k
        assert minimal == [list(range(k))]
        tuple_results.append({
            "tuple_length": k,
            "minimum_finite_pool_support": minimum,
            "minimum_supports": minimal,
            "all_supports_in_finite_pool": len(supports),
        })

    witnesses = []
    dimension_counts = {}
    for d in range(1, 4):
        k = d + 1
        code = tuple_code([Atom(i) for i in range(k)])
        count = 0
        for f in subsets(n, d):
            i = next(i for i in range(k) if i not in f)
            j = next(j for j in range(n) if j not in f and j != i)
            p = transpose(n, i, j)
            assert fixes(p, f)
            assert act(code, p) != code
            witnesses.append({"dimension": d, "candidate_support": sorted(f),
                              "transposition": [i, j]})
            count += 1
        dimension_counts[str(d)] = count

    # Finite groups have spurious co-large supports. In the infinite theorem,
    # supports must be finite subsets of an infinite index set.
    atom = Atom(0)
    support_one = frozenset((0,))
    support_complement = frozenset(range(1, n))
    actual_supports = supporting_subsets(atom, ps, all_subsets)
    assert support_one in actual_supports
    assert support_complement in actual_supports
    assert support_one & support_complement not in actual_supports

    # Equivariance alone does not preserve support: first projection forgets
    # its second coordinate; the orbit quotient of atoms forgets all indices.
    p = transpose(n, 1, 2)
    assert act(Atom(0), p) == Atom(0)
    assert act(Atom(1), p) != Atom(1)
    orbit_quotient = lambda _atom: 0
    for g in ps:
        for i in range(n):
            assert orbit_quotient(act(Atom(i), g)) == orbit_quotient(Atom(i))

    # A pure code has empty support, so the no-go theorem permits it.
    empty = frozenset()
    pure_code = kuratowski(empty, frozenset((empty,)))
    assert all(act(pure_code, p) == pure_code for p in ps)

    return {
        "status": "PASS",
        "scope": "Exact finite diagnostics only; no infinite-schema or machine theorem",
        "finite_index_count": n,
        "permutation_count": len(ps),
        "factorization": {
            "support_size_cap": 2,
            "support_pair_count": len(small_supports) ** 2,
            "decompositions_checked": decompositions,
            "by_intersection_size": by_intersection,
        },
        "kuratowski_tuple_stabilizers": {
            "comparisons": stabilizer_comparisons,
            "results": tuple_results,
        },
        "dimension_obstruction": {
            "candidate_support_witness_counts": dimension_counts,
            "total_witnesses": len(witnesses),
            "witnesses": witnesses,
        },
        "negative_controls": {
            "finite_support_intersection_fails_for_complementary_large_support": {
                "first": sorted(support_one),
                "second": sorted(support_complement),
                "intersection_supports_atom": False,
            },
            "projection_loses_support_without_injectivity": True,
            "orbit_quotient_erases_all_atom_support": True,
            "pure_kuratowski_code_has_empty_support": True,
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(json.dumps({
        "status": result["status"],
        "decompositions": result["factorization"]["decompositions_checked"],
        "tuple_stabilizer_comparisons": result["kuratowski_tuple_stabilizers"]["comparisons"],
        "dimension_witnesses": result["dimension_obstruction"]["total_witnesses"],
        "output": str(args.output) if args.output else None,
    }, sort_keys=True))


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled; Python -O is unsupported")
    main()
