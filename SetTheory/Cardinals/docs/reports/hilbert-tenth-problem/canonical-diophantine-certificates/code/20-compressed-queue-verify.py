"""Reproduce finite checks. These supplement, not replace, the article's proofs."""
from __future__ import annotations
from itertools import product
from math import gcd, lcm
from pathlib import Path
import json
import random
import sys

from queue_certificates import (
    Action, Leaf, Concat, chain, run, encode, summarize, expand,
    compose_resource, power_resource, power_word, compile_certificate,
    trace_data, maximum_repetitions, pumping_bound, periodic_conjugacy,
    compile_infinite_certificate, binary_chain_length,
)

ROOT = Path(__file__).resolve().parents[1]
RNG = random.Random(20261002)
COUNTS: dict[str, int] = {}


def check(name: str, assertion: bool) -> None:
    if not assertion:
        raise AssertionError(f"failed: {name}; completed checks: {COUNTS}")
    COUNTS[name] = COUNTS.get(name, 0) + 1


def words(maximum: int) -> list[str]:
    return ["".join(p) for n in range(maximum + 1) for p in product("01", repeat=n)]


def main() -> None:
    # Unique min/complementarity gadget; independently enumerate ALL candidates
    # that could satisfy its two sum equations on this finite input range.
    for s, r in product(range(9), repeat=2):
        sols = [(c, s - c, r - c) for c in range(min(s, r) + 1)
                if (s - c) * (r - c) == 0]
        check("unique_min_gadget", sols == [(min(s, r), max(s-r, 0), max(r-s, 0))])

    pairs = list(product(range(4), repeat=2))
    for x, y, z in product(pairs, repeat=3):
        check("resource_associativity", compose_resource(compose_resource(x, y), z)
              == compose_resource(x, compose_resource(y, z)))

    endpoints = words(2)
    acts = [Action(a, b) for a in "01" for b in words(2)]
    # 2,954 nonempty traces, each with seven inputs and seven target words.
    for size in range(1, 4):
        for trace in product(acts, repeat=size):
            u, v, r, s = trace_data(trace)
            for q in endpoints:
                actual = run(trace, q)
                for out in endpoints:
                    predicted = len(q) >= r and q + v == u + out
                    check("endpoint_equivalence", predicted == (actual is not None and actual == out))
                check("resource_drift", s-r == len(v)-len(u))
                # Direct, independent prefix-deficit calculation.
                need, balance = 0, 0
                for action in trace:
                    need = max(need, len(action.read)-balance)
                    balance += len(action.write)-len(action.read)
                check("resource_prefix_formula", need == r)

    # Arbitrary finite read/write words, including empty words.
    for _ in range(5000):
        trace = [Action(RNG.choice(words(3)), RNG.choice(words(3)))
                 for _ in range(RNG.randrange(1, 6))]
        q = RNG.choice(words(5))
        out = RNG.choice(words(5))
        u, v, r, s = trace_data(trace)
        check("atomic_multisymbol_endpoint", (len(q) >= r and q+v == u+out)
              == (run(trace, q) == out))
        k = RNG.randrange(1, 9)
        _, _, rk, sk = trace_data(trace*k)
        check("power_resource_formula", power_resource((r, s), k) == (rk, sk))
        check("power_read_encoding", power_word(encode(u), k) == encode(u*k))
        check("power_write_encoding", power_word(encode(v), k) == encode(v*k))

    # Finite certificate compilation, including valid and invalid endpoints.
    accepted = 0
    for _ in range(700):
        # A small acyclic grammar with substantial DAG reuse.
        nodes = [Leaf(RNG.choice(acts)) for _ in range(3)]
        for _ in range(RNG.randrange(1, 9)):
            nodes.append(Concat(RNG.randrange(len(nodes)), RNG.randrange(len(nodes))))
        trace = expand(nodes)
        q = RNG.choice(words(5))
        result = run(trace, q)
        target = result if result is not None and RNG.randrange(2) else RNG.choice(words(4))
        cert = compile_certificate(nodes, q, target)
        check("SLP_certificate_equivalence", cert.accepts() == (result == target))
        leaves = sum(isinstance(n, Leaf) for n in nodes)
        concats = len(nodes) - leaves
        check("exact_variable_count", len(cert.names) == 6*len(nodes)+3*concats+1)
        check("exact_residual_count", len(cert.residuals) == 6*leaves+9*concats+3)
        check("residual_degree_bound", all(p.degree <= 2 for p in cert.residuals))
        check("quartic_degree_bound", cert.polynomial().degree <= 4)
        check("SOS_evaluation", cert.polynomial().evaluate(cert.witness)
              == sum(p.evaluate(cert.witness)**2 for p in cert.residuals))
        if cert.accepts():
            accepted += 1
            for j in range(len(cert.witness)):
                for delta in (-1, 1):
                    mutated = cert.witness.copy()
                    mutated[j] += delta
                    if mutated[j] >= 0:
                        check("single_coordinate_mutation_rejected", not cert.accepts(mutated))
    check("accepted_random_certificate_examples", accepted >= 20)

    # Word periodicity: all binary words of lengths 1..5 and all phase shifts.
    periods = words(5)[1:]
    for u, v in product(periods, repeat=2):
        a, b = len(u), len(v)
        threshold = a+b-gcd(a, b)
        for shift in range(a):
            prefix_equal = all(u[(shift+i) % a] == v[i % b] for i in range(threshold))
            cycle_equal = all(u[(shift+i) % a] == v[i % b] for i in range(lcm(a, b)))
            check("Fine_Wilf_all_binary_periods", prefix_equal == cycle_equal)

    # Exact macro iteration and finite conjugacy, with arbitrary internal order.
    loop_cases = 0
    infinity_cases = 0
    for _ in range(6000):
        trace = [RNG.choice(acts) for _ in range(RNG.randrange(1, 5))]
        q = RNG.choice(words(4))
        nmax = maximum_repetitions(trace, q)
        check("infinite_loop_conjugacy", periodic_conjugacy(trace, q) == (nmax is None))
        current = q
        if nmax is None:
            infinity_cases += 1
            count = max(20, pumping_bound(trace, q))
            for _ in range(count):
                current = run(trace, current)
                check("infinite_loop_finite_crosscheck", current is not None)
        else:
            for _ in range(nmax):
                current = run(trace, current)
                check("exact_macro_count_success", current is not None)
            check("exact_macro_count_first_failure", run(trace, current) is None)
        u, v, _, _ = trace_data(trace)
        if len(v) >= len(u):
            bound = pumping_bound(trace, q)
            current = q
            for _ in range(bound):
                if current is None:
                    break
                current = run(trace, current)
            check("finite_pumping_test", (current is not None) == (nmax is None))
        loop_cases += 1

    # The ordinary quartic infinite-loop compiler, with no Pow predicate.
    for _ in range(800):
        trace = [RNG.choice(acts) for _ in range(RNG.randrange(1, 5))]
        nodes = chain(trace)
        q = RNG.choice(words(4))
        infcert = compile_infinite_certificate(nodes, q)
        check("infinite_quartic_equivalence", infcert.accepts()
              == (maximum_repetitions(trace, q) is None))
        check("infinite_quartic_degree", infcert.polynomial().degree <= 4)
        u, v, _, _ = trace_data(trace)
        a, b = len(u), len(v)
        if b >= a:
            d = gcd(a, b)
            h = binary_chain_length(b//d)+binary_chain_length(a//d)
            c = sum(isinstance(n, Concat) for n in nodes)
            check("infinite_quartic_variable_count", len(infcert.names) == 6*len(nodes)+3*c+2*h+1)
            if infcert.accepts():
                for j in range(len(infcert.witness)):
                    altered = infcert.witness.copy()
                    altered[j] += 1
                    check("infinite_witness_mutation_rejected", not infcert.accepts(altered))
    grow = compile_infinite_certificate([Leaf(Action("1", "11"))], "1")
    check("growing_queue_infinite_quartic", grow.accepts())
    grow.export(str(ROOT / "data" / "infinite_growth_quartic.json"))
    empty_read = compile_infinite_certificate([Leaf(Action("", "1"))], "")
    check("read_free_loop_trivial_certificate", empty_read.accepts() and len(empty_read.names) == 0)

    # The 'ghost read' counterexample: word identity true, chronology false.
    ghost = [Action("0", ""), Action("1", "1")]
    u, v, r, _ = trace_data(ghost)
    check("ghost_word_identity", "0"+v == u)
    check("ghost_resource_rejected", len("0") < r and run(ghost, "0") is None)
    check("ghost_quartic_rejected", not compile_certificate(chain(ghost), "0", "").accepts())

    # An instance attaining the stated whole-macro pumping bound.
    sharp = [Action("0", "010"), Action("1", "")]
    check("sharp_macro_example", maximum_repetitions(sharp, "01") == 2
          and pumping_bound(sharp, "01") == 3)

    # Big natural-number witness, generated WITHOUT trace expansion.
    doubling = [Leaf(Action("1", "1"))]
    for _ in range(16):
        doubling.append(Concat(len(doubling)-1, len(doubling)-1))
    big = compile_certificate(doubling, "1", "1")
    check("exponential_trace_certificate", big.accepts())
    check("exponential_trace_steps", big.summaries[-1].steps == 65536)
    check("exponential_trace_counts", len(big.names) == 151 and len(big.residuals) == 153)
    check("exponential_trace_scale", big.summaries[-1].pu == 3**65536)
    check("exponential_trace_content", big.summaries[-1].cu == big.summaries[-1].pu-1)
    check("exponential_trace_expanded_polynomial", big.polynomial().evaluate(big.witness) == 0)

    # Nontrivial binary example used in the article and exported as a polynomial.
    example = [Leaf(Action("0", "010")), Leaf(Action("1", "")), Concat(0, 1), Concat(2, 2)]
    example_cert = compile_certificate(example, "01", "0010")
    check("exported_example_valid", example_cert.accepts())
    example_cert.export(str(ROOT / "data" / "example_quartic.json"))

    # Structural validation rejects a control mismatch rather than ignoring it.
    try:
        compile_certificate([Leaf(Action("1", "1", 0, 1)),
                             Leaf(Action("1", "1", 0, 1)), Concat(0, 1)], "1", "1")
    except ValueError:
        check("control_mismatch_rejected", True)
    else:
        raise AssertionError("control mismatch was silently accepted")

    result = {
        "status": "PASS", "seed": 20261002, "python": sys.version.split()[0],
        "checks": COUNTS, "total_checks": sum(COUNTS.values()),
        "random_accepted_certificates": accepted, "random_loop_cases": loop_cases,
        "random_infinite_loop_cases": infinity_cases,
        "doubling": {"grammar_nodes": len(doubling), "expanded_steps": 65536,
                     "variables": len(big.names), "residuals": len(big.residuals),
                     "degree": big.polynomial().degree,
                     "scale_bit_length": big.summaries[-1].pu.bit_length(),
                     "sparse_polynomial_monomials": len(big.polynomial().terms)},
        "exported_example": {"variables": len(example_cert.names),
                             "residuals": len(example_cert.residuals),
                             "degree": example_cert.polynomial().degree,
                             "monomials": len(example_cert.polynomial().terms)},
        "limitations": ["Finite tests are not a formal proof.",
                        "The theorem proofs are in article.tex.",
                        "No universal cyclic-tag program or Lean kernel build was tested.",
                        "Powered-grammar identities are tested; the exporter emits ordinary SLP quartics."]
    }
    out = ROOT / "data" / "verification.json"
    out.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
