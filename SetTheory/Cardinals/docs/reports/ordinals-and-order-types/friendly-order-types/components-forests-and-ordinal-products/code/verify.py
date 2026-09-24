#!/usr/bin/env python3
"""Reproduce every computational claim in the article.

Run from any directory: python3 path/to/code/verify.py
Outputs are written to the adjacent data/ directory. No network or third-party
packages are used. The finite checks support, but do not replace, the proofs.

Two independent finite engines are exercised here.

* ``friendly.Poset`` carries the protected-root non-cut construction, the
  spanning-forest certificate verifier, lexicographic substitution, duals, and
  the efficient ideal-based enumeration of naturally labelled orders.  It
  drives the primary exhaustive run through support size seven.
* ``finite_posets.FinitePoset`` is a separate representation with its own
  validation, its own residual dynamic program, its own constructive
  certificate routine, and the height/width/product machinery used by the
  compositionality counterexample.  It re-derives the same values on the
  smaller range, so agreement is agreement between two implementations.

``ordinal_cnf`` supplies exact hereditary Cantor normal forms below epsilon_0
for the symbolic ordinal checks.
"""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import platform
import sys
import time
from collections import Counter
from functools import lru_cache
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from finite_posets import FinitePoset, naturally_labelled_posets  # noqa: E402
from friendly import Poset, bits, natural_lower_sets  # noqa: E402
from ordinal_cnf import (Ord, ZERO, ONE, OMEGA, natural_product,  # noqa: E402
                         ordinal_box_friendly, mixed_product_friendly)

EXAMPLE_NAMES = ("diamond.json", "chain_plus_isolate.json",
                 "N_poset.json", "empty.json")


def check(condition: bool, explanation: str) -> None:
    # Do not rely on Python assert: these tests still run under python -O.
    if not condition:
        raise AssertionError(explanation)


# --------------------------------------------------------------------------
# Primary exhaustive enumeration (friendly.Poset engine)
# --------------------------------------------------------------------------

def exhaustive_checks(max_n: int) -> tuple[dict, list[dict], list[str]]:
    """Every naturally labelled order through ``max_n``, including the empty one.

    Passing from size n-1 to size n chooses the strict predecessor set of the
    new largest label among the order ideals of the previous order, so every
    natural order arises exactly once.
    """
    rows: list[dict] = []
    log: list[str] = []
    connected_lemma_checks = 0
    for n in range(max_n + 1):
        count = 0
        hist: Counter[int] = Counter()
        for lower in natural_lower_sets(n):
            p = Poset._from_natural_lower(lower)
            direct = p.friendly_dp()
            formula = p.friendly()
            check(direct == formula, f"Rank mismatch n={n}, lower={lower}")
            check(p.dual().friendly_dp() == direct, f"Dual rank mismatch {lower}")
            p.check_certificate(p.optimal_certificate())
            if n >= 2 and len(p.components()) == 1:
                x = p.maximal_noncut(p.full)
                check(p.upper[x] == 1 << x, "Non-cut choice was not maximal")
                check(len(p.components(p.full & ~(1 << x))) == 1,
                      "Non-cut deletion disconnected the graph")
                connected_lemma_checks += 1
            count += 1
            hist[direct] += 1
        rows.append({"n": n, "naturally_labelled_posets": count,
                     "rank_histogram": {str(k): hist[k] for k in sorted(hist)}})
        line = f"n={n}: {count} cases, ranks={dict(sorted(hist.items()))}"
        log.append(line)
        print(line, flush=True)
    summary = {"maximum_n": max_n,
               "total_naturally_labelled_posets":
                   sum(r["naturally_labelled_posets"] for r in rows),
               "connected_maximal_noncut_checks": connected_lemma_checks,
               "checks_per_poset": ["graph formula vs residual DP",
                                    "dual residual DP",
                                    "optimal-sequence simulation and "
                                    "spanning-forest verification"]}
    return summary, rows, log


# --------------------------------------------------------------------------
# Composition laws (friendly.Poset engine)
# --------------------------------------------------------------------------

def composition_checks(log: list[str]) -> dict:
    base_orders = [Poset._from_natural_lower(lo)
                   for n in range(5) for lo in natural_lower_sets(n)]
    product_cases = 0
    middle_component_cases = 0
    for a, b in itertools.product(base_orders, repeat=2):
        prod = a.cartesian(b)
        if a.n == 0 or b.n == 0:
            expected = 0
        elif a.n == 1:
            expected = b.friendly()
        elif b.n == 1:
            expected = a.friendly()
        else:
            expected = (a.n * b.n - 1 - int(a.has_least() and b.has_least())
                        - int(a.has_greatest() and b.has_greatest()))
        check(prod.friendly() == expected, "Cartesian component formula failed")
        check(prod.friendly_dp() == expected, "Cartesian independent DP failed")
        if a.n >= 2 and b.n >= 2:
            nontrivial = [c for c in prod.components() if c.bit_count() > 1]
            check(len(nontrivial) == 1, "Unique non-endpoint product component")
            middle_component_cases += 1
        product_cases += 1
    line = (f"Cartesian products: {product_cases} cases, independent DP included; "
            f"{middle_component_cases} unique-middle-component checks")
    log.append(line)
    print(line, flush=True)

    fibers = [Poset.from_relations(1, []), Poset.from_relations(2, [(0, 1)]),
              Poset.from_relations(2, []), Poset.from_relations(3, [(0, 1), (1, 2)])]
    substitution_cases = 0
    for base in base_orders:
        for assignment in itertools.product(fibers, repeat=base.n):
            expected = 0
            for comp in base.components():
                labels = list(bits(comp))
                expected += (assignment[labels[0]].friendly() if len(labels) == 1
                             else sum(assignment[i].n for i in labels) - 1)
            lex = base.substitute(assignment)
            check(lex.friendly() == expected, "Substitution component formula failed")
            check(lex.friendly_dp() == expected, "Substitution independent DP failed")
            substitution_cases += 1
    line = (f"Heterogeneous substitutions: {substitution_cases} cases, "
            f"independent DP included")
    log.append(line)
    print(line, flush=True)

    subset_cases = 0
    root_certificate_cases = 0
    for n in range(6):
        for lower in natural_lower_sets(n):
            p = Poset._from_natural_lower(lower)
            target = p.friendly()
            comps = p.components()
            for selected in range(1 << n):
                if selected.bit_count() != target:
                    continue

                @lru_cache(None)
                def restricted_rank(mask: int, _p=p, _sel=selected) -> int:
                    return max((1 + restricted_rank(mask & ~_p.upper[x])
                                for x in bits(mask & _sel) if _p.inc[x] & mask),
                               default=0)

                actual = restricted_rank(p.full) == target
                expected = all((c & ~selected).bit_count() == 1 and
                               p.lower[next(bits(c & ~selected))] & c == (c & ~selected)
                               for c in comps)
                check(actual == expected,
                      "Maximum-friendly-subset classification failed")
                if expected:
                    roots = list(bits(p.full & ~selected))
                    certificate = p.optimal_certificate(roots)
                    p.check_certificate(certificate)
                    choices = sum(1 << step["choice"] for step in certificate["steps"])
                    check(choices == selected,
                          "Protected-root certificate used the wrong subset")
                    root_certificate_cases += 1
                subset_cases += 1
    line = (f"Maximum friendly subsets: {subset_cases} candidates, "
            f"{root_certificate_cases} protected-root certificates")
    log.append(line)
    print(line, flush=True)

    return {"cartesian_pairs": product_cases,
            "cartesian_factor_sizes": "0 through 4; product support at most 16",
            "unique_middle_component_checks": middle_component_cases,
            "heterogeneous_substitutions": substitution_cases,
            "substitution_fibers":
                "singleton, 2-chain, 2-antichain, 3-chain; base size <=4",
            "maximum_subset_candidates": subset_cases,
            "protected_root_certificates": root_certificate_cases,
            "maximum_subset_support_bound": 5}


def check_invalid_inputs() -> int:
    """Malformed orders and malformed friend claims must all be rejected."""
    rejected = 0
    cases = [lambda: Poset.from_relations(2, [(0, 1), (1, 0)]),
             lambda: Poset.from_relations(2, [(0, 2)]),
             lambda: Poset.from_relations(2, [(0, 0)]),
             lambda: Poset.from_relations(-1, []),
             lambda: Poset([3, 6, 4]),
             lambda: Poset([0]),
             lambda: Poset.from_relations(2, [(True, 1)])]
    for make in cases:
        try:
            make()
        except ValueError:
            rejected += 1
        else:
            raise AssertionError("An invalid poset was accepted")
    chain = Poset.from_relations(2, [(0, 1)])
    try:
        chain.check_certificate({"rank": 1, "steps": [{"choice": 0, "friend": 1}]},
                                require_optimal=False)
    except ValueError:
        rejected += 1
    else:
        raise AssertionError("A comparable friend was accepted")
    return rejected


# --------------------------------------------------------------------------
# Second engine: constructive certificates and the counterexample
# --------------------------------------------------------------------------

def second_engine_checks() -> tuple[dict, dict]:
    """The independent FinitePoset implementation over the smaller range.

    This is not the report's exhaustive-enumeration figure; it is a
    cross-implementation check on the same naturally labelled orders through
    size six, using a different representation, a different enumerator, and a
    different (search-based) constructive-certificate routine.
    """
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
            q = Poset(p.up, validate=False)
            check(q.friendly() == direct, f"Cross-engine disagreement: {p.up}")
            count += 1
        by_size[str(n)] = count
        total += count
        print(f"Second engine, n={n}: {count} passed", flush=True)

    d = FinitePoset.from_relations(4, [(0, 1), (0, 2), (1, 3), (2, 3)])
    e = FinitePoset.from_relations(4, [(0, 2), (1, 2), (2, 3)])
    k = FinitePoset.chain(2)
    check(d.invariants() == e.invariants() == (4, 3, 2, 1), "Factor invariants")
    dk, ek = d.product(k), e.product(k)
    check(dk.invariants() == (8, 4, 3, 5), "First product invariants")
    check(ek.invariants() == (8, 4, 3, 6), "Second product invariants")
    certificate = {"index_convention": "Product index = 2 * base_index + chain_index",
                   "invariant_order": ["maximal_order_type", "height", "width",
                                       "friendly_order_type"]}
    for name, p in [("D", d), ("E", e), ("K", k), ("D_times_K", dk), ("E_times_K", ek)]:
        rank, sequence, states = p.exact_rank()
        certificate[name] = {"upsets": p.up, "covers": p.covers(),
                             "invariants": p.invariants(), "endpoints": p.endpoints(),
                             "incomparability_components":
                                 [list(i for i in range(p.n) if (c >> i) & 1)
                                  for c in p.components()],
                             "optimal_friendly_sequence": sequence,
                             "direct_dp_states": states}
    # The three-element non-product separation of Section 6.1.
    u = FinitePoset.from_relations(3, [(0, 1), (0, 2)])
    w = FinitePoset.from_relations(3, [(0, 1)])
    check(u.invariants()[:3] == w.invariants()[:3] == (3, 2, 2),
          "Three-element separation: elementary invariants must agree")
    check(u.exact_rank()[0] == 1 and w.exact_rank()[0] == 2,
          "Three-element separation: friendly types must be 1 and 2")
    # The largest possible gap at fixed elementary invariants, Section 6.4.
    separation_cases = 0
    for n in range(3, 8):
        # L_n = chain(n-2) + antichain(2): a chain below two incomparable maxima.
        left = FinitePoset.from_relations(
            n, [(i, i + 1) for i in range(n - 3)] + [(n - 3, n - 2), (n - 3, n - 1)])
        # R_n = chain(n-1) disjoint-union chain(1): one vertex incomparable to all.
        right = FinitePoset.from_relations(n, [(i, i + 1) for i in range(n - 2)])
        separation_cases += 1
        check(left.component_formula() == 1, f"L_{n} must have friendly type 1")
        check(right.component_formula() == n - 1,
              f"R_{n} must have friendly type {n - 1}")
        check(left.height() == right.height() == n - 1, "Heights must agree")
        check(left.width() == right.width() == 2, "Widths must agree")
    return {"naturally_labelled_by_size": by_size, "nonempty_posets": total,
            "empty_posets": 1,
            "constructive_certificates_checked": total,
            "cross_engine_agreement_checked": total,
            "scope": "Cross-implementation check through size six; the report's "
                     "exhaustive-enumeration figure is the size-seven run above",
            "counterexample_verified": True,
            "separation_examples_verified": separation_cases}, certificate


# --------------------------------------------------------------------------
# Transfinite corner strategy (finite surrogates only)
# --------------------------------------------------------------------------

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


# --------------------------------------------------------------------------
# Symbolic ordinal arithmetic
# --------------------------------------------------------------------------

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


# --------------------------------------------------------------------------
# Generating function and shipped examples
# --------------------------------------------------------------------------

def generating_function_check(rows: list[dict]) -> dict:
    """Rebuild the rank histograms from A(z) = 1/(1 - B(z))."""
    nmax = len(rows) - 1
    a = [row["naturally_labelled_posets"] for row in rows]
    check(a[0] == 1 and all(row["n"] == n for n, row in enumerate(rows)),
          "Expected consecutive sizes starting from the empty poset")
    b = [0] * (nmax + 1)
    for n in range(1, nmax + 1):
        b[n] = a[n] - sum(b[i] * a[n - i] for i in range(1, n))
    f = [[0] * (nmax + 1) for _ in range(nmax + 1)]
    f[0][0] = 1
    for n in range(1, nmax + 1):
        for m in range(1, n + 1):
            for k in range(m - 1, n + 1):
                f[n][k] += b[m] * f[n - m][k - m + 1]
    for n, row in enumerate(rows):
        expected = {str(k): count for k, count in enumerate(f[n]) if count}
        check(expected == row["rank_histogram"],
              f"Generating-function mismatch at size {n}")
    print(f"Generating function: A=1/(1-B) reproduces all {nmax + 1} histograms",
          flush=True)
    return {"status": "PASS", "maximum_n": nmax, "connected_counts": b[1:],
            "method": "A=1/(1-B), followed by weighted component convolution",
            "limitation": "Consistency check on saved counts, "
                          "not an independent poset enumeration"}


def example_checks(examples_dir: Path) -> dict:
    out: dict = {}
    for name in EXAMPLE_NAMES:
        path = examples_dir / name
        if not path.exists():
            continue
        data = json.loads(path.read_text(encoding="utf-8"))
        p = Poset.from_relations(data["n"], data.get("relations", []))
        certificate = p.optimal_certificate(data.get("roots"))
        p.check_certificate(certificate)
        check(p.friendly_dp() == p.friendly(), f"Example DP mismatch: {name}")
        out[name] = {"input": data, "friendly_order_type": p.friendly(),
                     "dp": p.friendly_dp(),
                     "components": [list(bits(c)) for c in p.ordered_components()],
                     "certificate": certificate}
    if "diamond.json" in out and "chain_plus_isolate.json" in out:
        check(out["diamond.json"]["friendly_order_type"] == 1
              and out["chain_plus_isolate.json"]["friendly_order_type"] == 3,
              "The two four-element examples must have ranks 1 and 3")
    print(f"Shipped examples: {len(out)} inputs evaluated and certified", flush=True)
    return out


# --------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    root = Path(__file__).resolve().parent.parent
    parser.add_argument("--output", "--out", dest="output", type=Path,
                        default=root / "data")
    parser.add_argument("--examples", type=Path, default=root / "examples")
    parser.add_argument("--max-n", type=int, default=7,
                        help="Upper support size for the exhaustive enumeration "
                             "(8 and 9 are expensive)")
    args = parser.parse_args()
    if not 0 <= args.max_n <= 9:
        parser.error("--max-n must lie in 0,...,9")
    args.output.mkdir(parents=True, exist_ok=True)

    start = time.perf_counter()
    exhaustive, rows, log = exhaustive_checks(args.max_n)
    composition = composition_checks(log)
    invalid_count = check_invalid_inputs()
    line = f"Malformed inputs and friend claims rejected: {invalid_count}"
    log.append(line)
    print(line, flush=True)
    second_engine, certificate = second_engine_checks()
    tails = tail_strategy_checks()
    ordinal, ordinal_examples = ordinal_checks()
    gf = generating_function_check(rows)
    examples = example_checks(args.examples)
    elapsed = round(time.perf_counter() - start, 3)

    finite_report = {"status": "PASS", "python": platform.python_version(),
                     "enumeration": "naturally labelled posets, not isomorphism "
                                    "classes or all labelings",
                     "exhaustive": rows,
                     **exhaustive, **composition,
                     "invalid_inputs_rejected": invalid_count,
                     "elapsed_seconds": elapsed,
                     "limitations": "Finite computation is not a proof for all "
                                    "finite or infinite posets; no Lean formalization."}

    results = {"status": "all checks passed",
               "python": platform.python_version(),
               "elapsed_seconds": elapsed,
               "exhaustive_finite": {**exhaustive,
                                     "invalid_inputs_rejected": invalid_count,
                                     "report_file": "finite_verification.json"},
               "composition": composition,
               "second_engine": second_engine,
               "generating_function": gf,
               "shipped_examples": sorted(examples),
               "tail_strategy": tails,
               "ordinal": ordinal}

    for name, data in [("verification_results.json", results),
                       ("finite_verification.json", finite_report),
                       ("counterexample_certificate.json", certificate),
                       ("ordinal_examples.json", ordinal_examples),
                       ("generating_function_check.json", gf),
                       ("examples_results.json", examples)]:
        (args.output / name).write_text(json.dumps(data, indent=2) + "\n",
                                        encoding="utf-8")
    (args.output / "finite_verification.txt").write_text(
        "\n".join(log) + "\n", encoding="utf-8")
    with (args.output / "rank_distribution.csv").open("w", newline="",
                                                      encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["n", "friendly_order_type", "naturally_labelled_posets"])
        for row in rows:
            for rank, count in row["rank_histogram"].items():
                writer.writerow([row["n"], rank, count])
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
