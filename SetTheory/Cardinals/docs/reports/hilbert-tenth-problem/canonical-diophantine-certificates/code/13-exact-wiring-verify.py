#!/usr/bin/env python3
"""Reproduce the finite tests accompanying the article.

Standard library only; run from any directory. These are executable checks,
not a proof-assistant verification or an independent scholarly review.
Default: compare results with the distributed receipt (ignoring elapsed time).
Use --write to regenerate the receipt and example sparse polynomial.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
from itertools import combinations, combinations_with_replacement, permutations, product
import json
from pathlib import Path
import random
import sys
import time

from wiring import (ARITY, Layout, Net, closure_loops, edges_of, involution,
                    matchings, port, rewrite, switch_context)
from parity import correlation, matching_count, partitions, representative, signed_sum
from diophantine_memory import build_memory, decimal_natural

ROOT = Path(__file__).resolve().parent.parent


def parity_tests() -> dict:
    cases, closings = 0, 0
    rows = []
    # Independent of the recurrence: form every doubled graph and count components.
    for n in range(1, 7):
        qs = list(matchings(range(2*n)))
        assert len(qs) == matching_count(n)
        for lam in partitions(n):
            m, other = representative(lam)
            total = sum((-1)**(closure_loops(m, q)+closure_loops(other, q)) for q in qs)
            assert total == signed_sum(lam), (lam, total, signed_sum(lam))
            cases += 1
            closings += len(qs)
            if n <= 4:
                h = Fraction(total, len(qs))
                rows.append({"cycle_half_lengths": lam, "correlation": str(h),
                             "disagreement_probability": str((1-h)/2)})
    bound_cases = 0
    for n in range(2, 31):
        for lam in partitions(n):
            active = tuple(k for k in lam if k > 1)
            if not active:
                continue
            h = correlation(lam)
            assert Fraction(-1, 3) <= h <= Fraction(1, 5), (lam, h)
            assert (h == Fraction(-1, 3)) == (active == (2,))
            assert (h == Fraction(1, 5)) == (active == (3,))
            bound_cases += 1
    context_cases = 0
    for n in range(2, 5):
        ms = list(matchings(range(2*n)))
        for m, other in combinations(ms, 2):
            for modulus in range(2, 6):
                q = switch_context(m, other, modulus)
                assert (closure_loops(m, q)-closure_loops(other, q)) % modulus
                assert len(set(m)-set(q)) in (0, 2)
                context_cases += 1
    return {"direct_enumeration_partition_cases": cases,
            "direct_enumeration_closing_graphs": closings,
            "sharp_bounds_and_equality_partitions_through_weight_30": bound_cases,
            "near_context_tests_moduli_2_through_5": context_cases,
            "small_table": rows}


def rule_tests() -> dict:
    counts = Counter()
    order_tests = 0
    max_increment = {}
    for a, b in product(ARITY, repeat=2):
        for free_count in (0, 2, 4):
            layout = Layout(2, 1, free_count)
            remaining = [port(c, p) for c, label in ((0, a), (1, b))
                         for p in range(1, ARITY[label]+1)] + list(layout.free_ports)
            for wires in matchings(remaining):
                for prior_loops in (0, 3):
                    net = Net({0: a, 1: b}, involution(((port(0, 0), port(1, 0)),)+wires),
                              prior_loops, layout.free_ports)
                    reference = rewrite(net, 0, 1, 0, layout, method="components")
                    s = ARITY[a] + ARITY[b]
                    for order in permutations(range(s)):
                        result = rewrite(net, 0, 1, 0, layout, join_order=order)
                        assert result.record() == reference.record()
                        order_tests += 1
                    inc = reference.loops-prior_loops
                    key = a+"/"+b
                    max_increment[key] = max(inc, max_increment.get(key, 0))
                    assert 0 <= inc <= 2
                    if a != b or a == "epsilon":
                        assert inc == 0
                    counts[key] += 1
    return {"component_splice_comparisons_all_join_orders": order_tests,
            "contexts_by_ordered_rule": dict(sorted(counts.items())),
            "max_new_loops_by_ordered_rule": dict(sorted(max_increment.items()))}


def delta_tests() -> dict:
    layout = Layout(4, 2)
    nets, steps = 0, 0
    terminal_count = Counter()
    for wires in matchings(range(1, 13)):
        net = Net({i: "delta" for i in range(4)}, involution(wires))
        net.validate()
        for u, v in net.active_pairs():
            a = rewrite(net, u, v, 0, layout)
            b = rewrite(net, u, v, 0, layout, method="components")
            assert a.record() == b.record()
            steps += 1
        # Enumerate every reduction order, retaining exact loop counts.
        def terminals(current: Net, depth: int):
            active = current.active_pairs()
            if not active:
                return {json.dumps(current.record(), sort_keys=True)}
            answer = set()
            for u, v in active:
                answer.update(terminals(rewrite(current, u, v, depth, layout), depth+1))
            return answer
        terminal_set = terminals(net, 0)
        assert len(terminal_set) == 1
        terminal = json.loads(next(iter(terminal_set)))
        terminal_count[f"cells={len(terminal['cells'])},loops={terminal['loops']}"] += 1
        nets += 1
    def example(wires):
        net = Net({i: "delta" for i in range(4)},
                  involution(tuple((x+1, y+1) for x, y in wires)))
        trace = [net.record()]
        step = 0
        while net.active_pairs():
            assert len(net.active_pairs()) == 1
            u, v = net.active_pairs()[0]
            net = rewrite(net, u, v, step, layout)
            trace.append(net.record())
            step += 1
        return net, trace
    a, at = example(((0,3),(1,7),(2,9),(4,10),(5,6),(8,11)))
    b, bt = example(((0,3),(1,7),(2,9),(4,10),(5,8),(6,11)))
    assert not a.cells and a.loops == 2
    assert len(b.cells) == 2 and not b.active_pairs() and b.loops == 0
    return {"four_cell_matchings": nets, "initial_enabled_rewrites": steps,
            "unique_terminal_forms_checked": nets,
            "terminal_distribution": dict(sorted(terminal_count.items())),
            "repository_example_A_trace_one_based_ports": at,
            "repository_example_B_trace_one_based_ports": bt}


def product_tests() -> dict:
    cases = 0
    for U in range(2, 7):
        for L in range(1, 6):
            B = U**L + 1
            seen = {}
            for row in combinations_with_replacement(range(U), L):
                v = 1
                for x in row:
                    v *= B+x
                assert v not in seen, (U, L, row, seen.get(v))
                seen[v] = row
                cases += 1
    # Deliberately undersized bases fail, illustrating why the proved scale matters.
    for B in range(1, 101):
        assert B*(B+(B+2)) == (B+1)*(B+B)
        assert (0, B+2) != (1, B)
    return {"collision_free_multisets_tested": cases, "small_base_counterexamples": 100}


def memory_tests(write: bool) -> dict:
    assert decimal_natural(0) == "0"
    assert decimal_natural(10**5000+7) == "1"+"0"*4999+"7"
    initial, final = [1, 2, 0], [3, 1, 0]
    events = [(0,1,3),(2,0,4),(0,3,3),(1,2,1),(2,4,0)]
    c, layout = build_memory(initial, events, final, 8)
    assert not c.failures()
    quartic = c.sos()
    assert quartic.degree == 4 and quartic.evaluate(c.values) == 0
    mutation_count = 0
    for j, role in enumerate(c.roles):
        if role != "witness":
            continue
        values = c.values.copy()
        values[j] += 1
        assert c.failures(values), c.names[j]
        assert quartic.evaluate(values) > 0
        mutation_count += 1
    rng = random.Random(20261002)
    random_valid, invalid_read, invalid_final = 0, 0, 0
    for _ in range(160):
        A, V, m = rng.randrange(1, 7), rng.randrange(2, 12), rng.randrange(1, 15)
        ini = [rng.randrange(V) for _ in range(A)]
        state = ini.copy()
        log = []
        for _ in range(m):
            a = rng.randrange(A)
            new = rng.randrange(V)
            log.append((a, state[a], new))
            state[a] = new
        valid, _ = build_memory(ini, log, state, V)
        assert not valid.failures()
        random_valid += 1
        j = rng.randrange(m)
        damaged = log.copy()
        a, old, new = damaged[j]
        damaged[j] = (a, (old+1) % V, new)
        bad, _ = build_memory(ini, damaged, state, V)
        assert any(s.startswith("memory_link") for s in bad.failures())
        invalid_read += 1
        changed = state.copy()
        a = rng.randrange(A)
        changed[a] = (changed[a]+1) % V
        bad, _ = build_memory(ini, log, changed, V)
        assert any(s.startswith("memory_link") for s in bad.failures())
        invalid_final += 1
    exported = c.export()
    exported["layout"] = layout
    path = ROOT/"results"/"example_memory_certificate.json"
    if write:
        path.write_text(json.dumps(exported, indent=2)+"\n")
    else:
        assert json.loads(path.read_text()) == json.loads(json.dumps(exported))
    return {"example_layout": layout, "example_statistics": c.stats(),
            "expanded_quartic_monomials": len(quartic.terms),
            "one_coordinate_witness_mutations_rejected": mutation_count,
            "random_valid_histories": random_valid,
            "inconsistent_read_histories_rejected": invalid_read,
            "inconsistent_final_memories_rejected": invalid_final}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate saved receipts")
    args = parser.parse_args()
    start = time.monotonic()
    result = {"status": "PASS", "verification_scope": "executable finite checks; not a Lean verification",
              "parity": parity_tests(), "rules": rule_tests(), "delta": delta_tests(),
              "products": product_tests(), "memory": memory_tests(args.write)}
    result["source_sha256"] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sorted((ROOT/"code").glob("*.py"))}
    # Round-trip tuples to their serialized representation before comparing.
    result = json.loads(json.dumps(result))
    receipt = ROOT/"results"/"verification.json"
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+"\n")
    else:
        assert json.loads(receipt.read_text()) == result, "saved receipt differs; inspect before regeneration"
    print(json.dumps({"status": result["status"], "elapsed_seconds": round(time.monotonic()-start, 3),
                      "receipt": str(receipt), "python": sys.version.split()[0]}, indent=2))


if __name__ == "__main__":
    main()
