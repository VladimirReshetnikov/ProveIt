#!/usr/bin/env python3
"""Reproduce every computational claim in the article.

Run from any directory: python3 path/to/code/verify.py
Outputs are written to the adjacent data/ directory. No network or third-party
packages are used. The finite checks support, but do not replace, the proofs.
"""
from __future__ import annotations

import argparse
import json
from itertools import product
from pathlib import Path

from finite_posets import FinitePoset, naturally_labelled_posets
from ordinal_cnf import (Ord, ZERO, ONE, OMEGA, natural_product,
                         ordinal_box_friendly, mixed_product_friendly)


def check(condition: bool, explanation: str) -> None:
    # Do not rely on Python assert: these tests still run under python -O.
    if not condition:
        raise AssertionError(explanation)


def finite_checks() -> tuple[dict, dict]:
    by_size, total = {}, 0
    check(FinitePoset(()).exact_rank()[0] == 0, "Empty-poset rank")
    for n in range(1, 7):
        count = 0
        for p in naturally_labelled_posets(n):
            direct, cert, _ = p.exact_rank()
            check(direct == p.component_formula(), f"Finite formula failed: {p.up}")
            constructed = p.constructive_certificate()
            check(len(constructed) == direct, f"Constructive strategy failed: {p.up}")
            p.check_certificate(cert)
            count += 1
        by_size[str(n)] = count
        total += count
        print(f"Finite posets, n={n}: {count} passed", flush=True)

    small = [p for n in range(2, 5) for p in naturally_labelled_posets(n)]
    products_checked = 0
    for a in small:
        for b in small:
            p = a.product(b)
            amin, amax = a.endpoints()
            bmin, bmax = b.endpoints()
            expected = p.n - 1 - int(amin and bmin) - int(amax and bmax)
            check(p.exact_rank()[0] == expected, "Finite product formula")
            nontrivial = [c for c in p.components() if c.bit_count() > 1]
            check(len(nontrivial) == 1, "Unique middle product component")
            products_checked += 1
    print(f"Ordered products: {products_checked} passed", flush=True)

    d = FinitePoset.from_relations(4, [(0, 1), (0, 2), (1, 3), (2, 3)])
    e = FinitePoset.from_relations(4, [(0, 2), (1, 2), (2, 3)])
    k = FinitePoset.chain(2)
    check(d.invariants() == e.invariants() == (4, 3, 2, 1), "Factor invariants")
    dk, ek = d.product(k), e.product(k)
    check(dk.invariants() == (8, 4, 3, 5), "First product invariants")
    check(ek.invariants() == (8, 4, 3, 6), "Second product invariants")
    certificate = {"index_convention": "Product index = 2 * base_index + chain_index",
                   "invariant_order": ["maximal_order_type", "height", "width", "friendly_order_type"]}
    for name, p in [("D", d), ("E", e), ("K", k), ("D_times_K", dk), ("E_times_K", ek)]:
        rank, sequence, states = p.exact_rank()
        certificate[name] = {"upsets": p.up, "covers": p.covers(),
                             "invariants": p.invariants(), "endpoints": p.endpoints(),
                             "incomparability_components": [list(i for i in range(p.n)
                                                                   if (c >> i) & 1)
                                                             for c in p.components()],
                             "optimal_friendly_sequence": sequence,
                             "direct_dp_states": states}
    return {"naturally_labelled_by_size": by_size, "nonempty_posets": total,
            "empty_posets": 1, "ordered_products": products_checked,
            "constructive_certificates_checked": total,
            "counterexample_verified": True}, certificate


def tail_strategy_checks() -> dict:
    """Finite surrogates test only the move/witness logic, NOT infinite ranks."""
    cutoff = 2
    cases = 0
    degenerate_skips = 0
    no_move_cases = 0
    small = [p for n in range(1, 4) for p in naturally_labelled_posets(n)]
    for r in range(1, 4):
        for tails in product(range(1, 4), repeat=r):
            for bpos in small:
                if r == 1 and bpos.n == 1:
                    degenerate_skips += 1
                    continue
                tops = tuple(cutoff + m - 1 for m in tails)
                points = set(product(*(range(t + 1) for t in tops), range(bpos.n)))
                tail = {p for p in points if all(p[i] >= cutoff for i in range(r))}
                core = points - tail
                remaining = set(points)
                selected = []

                def leq(x: tuple[int, ...], y: tuple[int, ...]) -> bool:
                    return all(x[i] <= y[i] for i in range(r)) and bool((bpos.up[x[-1]] >> y[-1]) & 1)

                def move(x: tuple[int, ...], friend: tuple[int, ...]) -> None:
                    check(x in remaining and friend in remaining, "Tail move: absent point")
                    check(not leq(x, friend) and not leq(friend, x), "Tail move: wrong friend")
                    remaining.difference_update(y for y in tuple(remaining) if leq(x, y))
                    selected.append(x)

                greatest = next((j for j, down in enumerate(bpos.down) if down == bpos.whole), None)
                if greatest is None:
                    for x in sorted(tail, reverse=True):
                        c = next(c for c in range(bpos.n) if not ((bpos.up[c] >> x[-1]) & 1))
                        move(x, (0,) * r + (c,))
                    check(len(selected) == len(tail), "No-greatest move count")
                elif len(tail) == 1:
                    # The proof uses subposet monotonicity here, not a move.
                    no_move_cases += 1
                    cases += 1
                    continue
                else:
                    edge = {(j,) + tops[1:] + (greatest,) for j in range(cutoff, tops[0] + 1)}
                    top = tops + (greatest,)
                    for x in sorted(edge - {top}, reverse=True):
                        if r >= 2:
                            friend = (tops[0], 0) + tops[2:] + (greatest,)
                        else:
                            b0 = next(b for b in range(bpos.n) if b != greatest)
                            friend = (tops[0], b0)
                        move(x, friend)
                    friend = (0,) + tops[1:] + (greatest,)
                    for x in sorted(tail - edge, reverse=True):
                        move(x, friend)
                    check(len(selected) == len(tail) - 1, "Greatest-element move count")
                check(remaining == core, "Tail strategy did not leave exactly the core")
                cases += 1
    print(f"Finite-surrogate tail strategies: {cases} passed", flush=True)
    return {"cases": cases, "no_move_cases": no_move_cases,
            "excluded_single_chain_cases": degenerate_skips,
            "cutoff": cutoff, "ordinal_factor_counts": [1, 2, 3],
            "tail_lengths": [1, 2, 3], "finite_factor_sizes": [1, 2, 3],
            "scope": "Move legality, witnesses, counts, residuals only; not transfinite ranks"}


def ordinal_checks() -> tuple[dict, list]:
    n = Ord.nat
    wp = Ord.omega_power
    w = OMEGA
    w2, w3 = wp(n(2)), wp(n(3))
    ww = wp(w)
    sample = [ZERO, ONE, n(2), n(3), w, w.add(ONE), w.add(n(2)),
              w.natural_product(n(2)), w2, w2.add(w).add(n(3)), ww, ww.add(w).add(n(4))]
    identities = 0
    for a in sample:
        for b in sample:
            check(a.natural_sum(b) == b.natural_sum(a), "Natural-sum commutativity")
            check(a.natural_product(b) == b.natural_product(a), "Natural-product commutativity")
            identities += 2
            for c in sample:
                check(a.natural_sum(b).natural_sum(c) == a.natural_sum(b.natural_sum(c)), "Sum associativity")
                check(a.natural_product(b).natural_product(c) == a.natural_product(b.natural_product(c)), "Product associativity")
                check(a.natural_product(b.natural_sum(c)) == a.natural_product(b).natural_sum(a.natural_product(c)), "Distributivity")
                check(a.add(b).add(c) == a.add(b.add(c)), "Ordinal-addition associativity")
                identities += 4
    check(ONE.add(w) == w and w.add(ONE) != w, "Ordinary addition, not natural addition")
    for a in sample:
        if a.is_successor:
            check(a.predecessor().add(ONE) == a, "Right predecessor")
    for a in range(6):
        for b in range(6):
            check(n(a).natural_sum(n(b)) == n(a + b), "Finite sum")
            check(n(a).natural_product(n(b)) == n(a * b), "Finite product")

    examples = [
        ("omega x 3", [w, n(3)], w.natural_product(n(3))),
        ("(omega+2) x 3", [w.add(n(2)), n(3)], w.natural_product(n(3)).add(n(5))),
        ("(omega+1) x (omega+1)", [w.add(ONE), w.add(ONE)], w2.add(w.natural_product(n(2)))),
        ("(omega+2) x (omega+3)", [w.add(n(2)), w.add(n(3))], w2.add(w.natural_product(n(5))).add(n(5))),
        ("(omega^2+3) x (omega+2)", [w2.add(n(3)), w.add(n(2))], w3.add(w2.natural_product(n(2))).add(w.natural_product(n(3))).add(n(5))),
        ("(omega^omega+omega+4) x (omega^2+2)", [ww.add(w).add(n(4)), w2.add(n(2))],
         wp(w.add(n(2))).add(ww.natural_product(n(2))).add(w3).add(w2.natural_product(n(4))).add(w.natural_product(n(2))).add(n(7)))
    ]
    out = []
    for title, factors, expected in examples:
        calculated = ordinal_box_friendly(factors)
        check(calculated == expected, f"CNF example {title}")
        out.append({"product": title, "maximal_order_type": str(natural_product(factors)),
                    "friendly_order_type": str(calculated), "friendly_cnf": calculated.to_json()})
    check(mixed_product_friendly([w.add(ONE)], 2, False) == w.natural_product(n(2)).add(n(2)), "Finite factor without a greatest")
    check(mixed_product_friendly([w.add(ONE)], 4, True) == w.natural_product(n(4)).add(n(3)), "Finite factor with greatest")
    check(ordinal_box_friendly([]) == ZERO, "Empty product is a singleton")
    check(ordinal_box_friendly([ZERO, w]) == ZERO, "Zero factor")
    check(ordinal_box_friendly([ONE, w]) == ZERO, "Single nontrivial factor")
    check(ordinal_box_friendly([n(2), n(3)]) == n(3), "Finite box")
    print(f"Ordinal algebra: {identities} sampled identity checks passed", flush=True)
    return {"sampled_algebra_identities": identities, "sample_size": len(sample),
            "worked_box_examples": len(examples), "notation_scope": "ordinals below epsilon_0",
            "scope": "Exact symbolic identities and formula evaluation; not a transfinite tree-rank oracle"}, out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent.parent / "data")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    finite, certificate = finite_checks()
    tails = tail_strategy_checks()
    ordinal, examples = ordinal_checks()
    results = {"status": "all checks passed", "finite": finite, "tail_strategy": tails, "ordinal": ordinal}
    for name, data in [("verification_results.json", results),
                       ("counterexample_certificate.json", certificate),
                       ("ordinal_examples.json", examples)]:
        (args.output / name).write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
