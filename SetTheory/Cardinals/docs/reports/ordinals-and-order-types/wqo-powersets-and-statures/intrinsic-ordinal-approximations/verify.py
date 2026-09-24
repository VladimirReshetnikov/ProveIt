#!/usr/bin/env python3
"""Finite and symbolic checks accompanying the article (not a formal proof).

Python 3.10+, standard library only.  Exhaustively checks naturally labelled
posets through five points (every isomorphism type occurs), bounded word and
multiset constructions, finite rectangles, and exact CNF identities.  It also
creates an independently enumerated table of finite-cap statistics.  The
omega-prefix formulas in that table are symbolic applications of the theorem,
not observations from finite simulation.
"""
from __future__ import annotations

import csv
import itertools as it
import json
from pathlib import Path
import sys
from typing import Callable

from ordinal_arithmetic import (Ordinal, ZERO, ONE, OMEGA, cnf, omega_power,
                                natural_sum, natural_product, milner_rado,
                                predecessor_sample, monomial_product_height)

ROOT = Path(__file__).resolve().parent


def elements(mask: int):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def posets(n: int):
    """All distinct transitive orders compatible with 0,1,...,n-1."""
    pairs = list(it.combinations(range(n), 2))
    seen = set()
    for bits in range(1 << len(pairs)):
        lower = [1 << j for j in range(n)]
        for k, (i, j) in enumerate(pairs):
            if bits >> k & 1:
                lower[j] |= 1 << i
        for j in range(n):
            for i in range(j):
                if lower[j] >> i & 1:
                    lower[j] |= lower[i]
        p = tuple(lower)
        if p not in seen:
            seen.add(p)
            yield p


def is_downset(p: tuple[int, ...], mask: int) -> bool:
    return all(p[i] & ~mask == 0 for i in elements(mask))


def is_directed(p: tuple[int, ...], mask: int) -> bool:
    if not mask:
        return False
    members = list(elements(mask))
    return all(any((p[k] >> i & 1) and (p[k] >> j & 1) for k in members)
               for i in members for j in members)


def downsets(p: tuple[int, ...]) -> list[int]:
    return [s for s in range(1 << len(p)) if is_downset(p, s)]


def downset_ranks(ds: list[int]) -> dict[int, int]:
    rank: dict[int, int] = {}
    for d in sorted(ds, key=int.bit_count):
        rank[d] = max((rank[c] + 1 for c in rank if c != d and c & ~d == 0),
                      default=0)
    return rank


def make_order(objects: list, leq: Callable) -> tuple[int, ...]:
    p = tuple(sum(1 << i for i, x in enumerate(objects) if leq(x, y))
              for y in objects)
    assert len(set(p)) == len(p), "construction not antisymmetric"
    return p


def word_leq(u: tuple, v: tuple, letter_leq: Callable) -> bool:
    for indices in it.combinations(range(len(v)), len(u)):
        if all(letter_leq(x, v[j]) for x, j in zip(u, indices)):
            return True
    return False


def multiset_leq(u: tuple, v: tuple, letter_leq: Callable) -> bool:
    return any(all(letter_leq(x, v[j]) for x, j in zip(u, indices))
               for indices in it.permutations(range(len(v)), len(u)))


def finite_checks() -> dict:
    counts, n_downsets, n_ideals, union_checks = {}, 0, 0, 0
    for n in range(6):
        count = 0
        for p in posets(n):
            count += 1
            ds = downsets(p)
            ideals = [d for d in ds if is_directed(p, d)]
            assert set(ideals) == set(p), ("finite ideals are principal", p)
            ranks = downset_ranks(ds)
            assert all(ranks[d] == d.bit_count() for d in ds)
            assert max(ranks.values()) + 1 == n + 1
            # Enumerate every finite family of ideals, including the empty one.
            families = list(range(1 << len(ideals)))
            unions = [0] * len(families)
            for f in families:
                for i in elements(f):
                    unions[f] |= ideals[i]
            assert set(unions) == set(ds)
            # Directed finite cover: Hoare order is exactly inclusion of unions.
            for f in families:
                for g in families:
                    hoare = all(any(ideals[i] & ~ideals[j] == 0
                                    for j in elements(g)) for i in elements(f))
                    assert hoare == (unions[f] & ~unions[g] == 0)
                    union_checks += 1
            n_downsets += len(ds)
            n_ideals += len(ideals)
        counts[str(n)] = count
    return {"naturally_labelled_posets_by_size": counts,
            "posets_total": sum(counts.values()), "downsets_checked": n_downsets,
            "ideals_checked": n_ideals, "Hoare_union_pair_checks": union_checks}


def bounded_checks() -> dict:
    bases = {"empty": (), "singleton": (1,), "chain2": (1, 3),
             "antichain2": (1, 2), "fork3": (1, 3, 5)}
    results = {}
    for name, p in bases.items():
        ideals = [s for s in downsets(p) if is_directed(p, s)]
        for kind in ("words", "multisets"):
            constructor = it.product if kind == "words" else it.combinations_with_replacement
            if kind == "words":
                objects = [v for k in range(3) for v in constructor(range(len(p)), repeat=k)]
                descriptions = [v for k in range(3) for v in constructor(ideals, repeat=k)]
            else:
                objects = [v for k in range(3) for v in constructor(range(len(p)), k)]
                descriptions = [v for k in range(3) for v in constructor(ideals, k)]
            embed = word_leq if kind == "words" else multiset_leq
            leq = lambda x, y: bool(p[y] >> x & 1)
            q = make_order(objects, lambda u, v: embed(u, v, leq))
            target_ideals = {s for s in downsets(q) if is_directed(q, s)}
            generated = []
            for description in descriptions:
                top_words = list(it.product(*(list(elements(i)) for i in description)))
                mask = sum(1 << j for j, u in enumerate(objects)
                           if any(embed(u, v, leq) for v in top_words))
                generated.append(mask)
            assert set(generated) == target_ideals
            assert len(generated) == len(set(generated))
            for i, a in enumerate(descriptions):
                for j, b in enumerate(descriptions):
                    ideal_embed = embed(a, b, lambda x, y: x & ~y == 0)
                    assert ideal_embed == (generated[i] & ~generated[j] == 0)
            results[f"{name}/{kind}/length<=2"] = {
                "objects": len(objects), "ideals": len(target_ideals),
                "isomorphism_pairs_checked": len(descriptions) ** 2}
    return results


def ordinal_checks() -> dict:
    checks = 0
    def check(predicate: bool, message: str):
        nonlocal checks
        if not predicate:
            raise AssertionError(message)
        checks += 1
    for n in range(10):
        for m in range(10):
            a, b = Ordinal.finite(n), Ordinal.finite(m)
            check(natural_sum(a, b) == Ordinal.finite(n + m), "finite sum")
            check(natural_product(a, b) == Ordinal.finite(n * m), "finite product")
    check(ONE + OMEGA == OMEGA, "1+w=w")
    check(OMEGA + ONE != ONE + OMEGA, "ordinary sum is not natural sum")
    check(natural_product(OMEGA + ONE, OMEGA + ONE) == cnf((2, 1), (1, 2), (0, 1)),
          "(w+1) natural square")
    for d in range(1, 5):
        for ns in it.product(range(1, 6), repeat=d):
            delta = milner_rado(*(Ordinal.finite(n) for n in ns))
            sums = {sum(xs) for xs in it.product(*(range(n) for n in ns))}
            check(delta == Ordinal.finite(sum(ns) - d + 1), "finite MR formula")
            check(sums == set(range(sum(ns) - d + 1)), "finite MR definition")
    examples = [
        ((OMEGA, OMEGA), OMEGA),
        ((OMEGA + ONE, OMEGA + ONE), cnf((1, 2), (0, 1))),
        ((OMEGA + ONE, OMEGA), cnf((1, 2))),
        ((cnf((2, 2), (1, 3), (0, 5)), cnf((2, 1), (1, 4))), cnf((2, 3), (1, 7))),
        ((omega_power(OMEGA), omega_power(OMEGA)), omega_power(OMEGA)),
        ((omega_power(OMEGA + ONE), omega_power(OMEGA)), omega_power(OMEGA + ONE)),
    ]
    for args, expected in examples:
        check(milner_rado(*args) == expected, "transfinite MR example")
        previous = ZERO
        for n in range(1, 15):
            sample = natural_sum(*(predecessor_sample(a, n) for a in args))
            check(sample < expected, "cofinal predecessor lower bound")
            check(previous <= sample, "monotone predecessor sample")
            previous = sample
    heights = [
        ("w x w", [ONE, ONE], [], (), OMEGA),
        ("w x (w+1)", [ONE], [ONE], (), cnf((2, 1))),
        ("(w+1) x (w+1)", [], [ONE, ONE], (), cnf((2, 1), (0, 1))),
        ("w^2 x w^2", [Ordinal.finite(2)] * 2, [], (), cnf((3, 1))),
        ("w^w x w^w", [OMEGA, OMEGA], [], (), omega_power(OMEGA)),
        ("(w^2+1) x (w+1)", [], [Ordinal.finite(2), ONE], (), cnf((3, 1), (0, 1))),
        ("3 x (w+1)", [], [ONE], (3,), cnf((1, 3), (0, 1))),
        ("3 x w", [ONE], [], (3,), OMEGA),
        ("3 x 4", [], [], (3, 4), Ordinal.finite(13)),
        ("empty factor", [ONE], [], (0,), ONE),
    ]
    for name, opened, closed, finite, expected in heights:
        check(monomial_product_height(opened, closed, finite) == expected, name)
    return {"exact_and_sample_checks": checks,
            "height_examples": {name: str(expected) for name, _, _, _, expected in heights}}


def cap_table() -> dict:
    rows = []
    cases = {"one point": (1,), "antichain 2": (1, 2), "antichain 3": (1, 2, 4),
             "chain 3": (1, 3, 7), "C3 disjoint C1": (1, 3, 7, 8),
             "C3 disjoint C2": (1, 3, 7, 8, 24), "fork with least": (1, 3, 5)}
    for name, p in cases.items():
        n = len(p)
        u = max(sum(bool(p[j] >> i & 1) for j in range(n)) for i in range(n))
        ranks = [0] * n
        for j in range(n):
            ranks[j] = max((ranks[i] + 1 for i in elements(p[j] & ~(1 << j))), default=0)
        height = max(ranks) + 1
        width = max(s.bit_count() for s in range(1 << n)
                    if all(not (p[j] >> i & 1) and not (p[i] >> j & 1)
                           for i, j in it.combinations(elements(s), 2)))
        # This also checks the important finite-prefix offset: +1, not +0.
        for m in range(4):
            prefix = [(1 << (i + 1)) - 1 for i in range(m)]
            q = tuple(prefix + [((1 << m) - 1) | (d << m) for d in p])
            r = downset_ranks(downsets(q))
            assert max(r.values()) + 1 == m + n + 1
        rows.append({"F": name, "size": n, "height": height, "width": width,
                     "max_upper_cone": u, "a_o(omega+F)": f"omega+{u}",
                     "h(P_f(omega+F))": f"omega+{n}",
                     "finite_tail_discrepancy": n - u})
    with (ROOT / "finite_cap_examples.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    return {"caps": len(rows), "finite_prefix_instances": 4 * len(rows),
            "warning": "omega-prefix outputs use proved symbolic formulas, not finite simulation"}


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O: the verification requires enabled assertions.")
    report = {"python": sys.version.split()[0],
              "scope": "Finite and exact symbolic checks; not a proof-assistant verification.",
              "finite_posets": finite_checks(), "bounded_constructions": bounded_checks(),
              "ordinal_arithmetic": ordinal_checks(), "finite_caps": cap_table(),
              "result": "PASS"}
    text = json.dumps(report, indent=2, sort_keys=True)
    (ROOT / "verification_report.json").write_text(text + "\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
