#!/usr/bin/env python3
"""Deterministic exact tests. These are executable evidence, not formal proofs."""
from __future__ import annotations
import argparse
import copy
import itertools
import json
import platform
import random
from pathlib import Path
import sympy as sp
from van_kampen import *


def check(condition: bool, description: str) -> None:
    if not condition:
        raise AssertionError(description)


def reduced_words(max_length: int):
    yield ""
    frontier = [""]
    for _ in range(max_length):
        frontier = [w+c for w in frontier for c in "aAbB"
                    if not w or w[-1] != c.swapcase()]
        yield from frontier


def run() -> dict:
    counts: dict[str, int] = {}
    matrices = {}
    for w in reduced_words(8):
        u = evaluate_word(w)
        check(u not in matrices, "finite-batch injectivity")
        matrices[u] = w
        check(chart(unchart(u)) == u, "chart round trip")
        check(evaluate_syllables(decode_sanov(u)) == u, "Sanov descent")
    counts["reduced_words_through_length_8"] = len(matrices)
    chart_points = 0
    for c in itertools.product(range(-8, 9), repeat=4):
        if chart_residual(c) == 0:
            u = chart(c)
            check(evaluate_syllables(decode_sanov(u)) == u, "chart-point decoding")
            chart_points += 1
    counts["chart_tuples_tested"] = 17**4
    counts["chart_integer_points_decoded"] = chart_points
    rng = random.Random(20261002)
    for _ in range(1000):
        word = "".join(rng.choice("aAbB") for _ in range(rng.randrange(81)))
        u = evaluate_word(word)
        check(evaluate_syllables(decode_sanov(u)) == u, "random Sanov decoding")
        check(evaluate_word(freely_reduce(word)) == u, "free reduction invariance")
    counts["random_word_round_trips"] = 1000

    options = [(j, evaluate_word(w)) for j in range(3) for w in ("", "a", "A", "b", "B")]
    positive, mutations = 0, 0
    for m in range(1, 4):
        for factors in itertools.product(options, repeat=m):
            witness = make_budget_witness(["abAB"], [j for j, _ in factors], [u for _, u in factors])
            residuals = budget_residuals(["abAB"], witness)
            check(len(residuals) == 13*m, "scalar residual count")
            check(not any(residuals), "valid budget certificate")
            for which in ("product", "selector", "boundary"):
                bad = copy.deepcopy(witness)
                if which == "product":
                    v = bad.products[0]
                    bad.products[0] = (v[0]+1, *v[1:])
                elif which == "selector":
                    bad.selectors[0][0] = 2
                else:
                    v = bad.boundary
                    bad.boundary = (v[0]+1, *v[1:])
                check(any(budget_residuals(["abAB"], bad)), "mutation rejected: "+which)
                mutations += 1
            positive += 1
    counts["valid_budget_certificates"] = positive
    counts["rejected_budget_mutations"] = mutations

    symbol_systems = 0
    symbolic_checks = 0
    for relators in (["abAB"], ["aa", "bbb"], ["aa", "bbb", "abAB"]):
        for m in range(1, 4):
            system = compile_budget(relators, m)
            s = len(relators)
            check(len(system.variables) == (2*s+13)*m-4, "budget arity")
            check(len(system.residuals) == (2*s+11)*m, "budget residual count")
            names = system.parameters+system.variables
            check(all(sp.Poly(r, *names).total_degree() <= 2 for r in system.residuals), "quadratic residuals")
            # The coefficient test of the SOS quartic is done for the smallest systems.
            if m == 1:
                check(sp.Poly(system.polynomial(True), *names).total_degree() <= 4, "quartic degree")
            for _ in range(8):
                labels = [rng.randrange(2*s+1) for _ in range(m)]
                us = [evaluate_word("".join(rng.choice("aAbB") for _ in range(5))) for _ in range(m)]
                witness = make_budget_witness(relators, labels, us)
                assignment = symbolic_budget_assignment(system, witness)
                symbolic = [int(r.xreplace(assignment)) for r in system.residuals]
                check(symbolic == budget_residuals(relators, witness), "symbolic/numerical agreement")
                check(not any(symbolic), "symbolic positive zero")
                symbolic_checks += 1
            symbol_systems += 1
    counts["budget_symbolic_systems"] = symbol_systems
    counts["budget_symbolic_numeric_crosschecks"] = symbolic_checks

    itinerary_checks = 0
    for m in range(1, 6):
        labels = [(1, 2, 0)[i % 3] for i in range(m)]
        words = [("", "abAB", "baBA")[j] for j in labels]
        system = compile_itinerary(words)
        check(len(system.variables) == 8*m-4, "itinerary arity")
        check(len(system.residuals) == 5*m, "itinerary equation count")
        check(all(sp.Poly(r, *(system.parameters+system.variables)).total_degree() <= 2
                  for r in system.residuals), "itinerary quadratic")
        us = [evaluate_word("a"*i+"B") for i in range(m)]
        witness = make_budget_witness(["abAB"], labels, us)
        d = symbolic_budget_assignment(system, witness)
        check(all(r.xreplace(d) == 0 for r in system.residuals), "itinerary positive zero")
        itinerary_checks += 1
    counts["itinerary_symbolic_systems"] = itinerary_checks

    # The omitted-hypothesis counterexamples must both be genuine failures.
    nonunimodular_chart = (1, 0, 0, 5)  # determinant 5, outside the group
    check(mul(nonunimodular_chart, power(A, 5)) == mul(A, nonunimodular_chart), "missing determinant false positive")
    check(chart_residual((0, 0, 0, 1)) == 1, "determinant residual detects false positive")
    J = (0, -1, 1, 0)
    check(conjugate(J, A) == inverse(B), "missing congruence false positive")
    try:
        unchart(J)
    except ValueError:
        pass
    else:
        raise AssertionError("chart accepted J")
    counts["omitted_hypothesis_counterexamples"] = 2

    grid_checks = 0
    for k in range(21):
        for ell in range(21):
            nodes = grid_dag(k, ell)
            values, costs = evaluate_dag(nodes, ["abAB"])
            check(values[-1] == rectangular_matrix(1 << k, 1 << ell), "grid boundary formula")
            check(costs[-1] == 1 << (k+ell), "expanded grid area")
            check(sum(n.kind == "product" for n in nodes) == k+ell, "optimal product count")
            grid_checks += 1
    counts["dyadic_grid_certificates"] = grid_checks
    values, costs = evaluate_dag(grid_dag(100, 100), ["abAB"])
    check(values[-1] == rectangular_matrix(1 << 100, 1 << 100), "large grid")
    counts["large_grid_expanded_area_bits"] = costs[-1].bit_length()

    grid_symbolic = 0
    for k, ell in ((0, 0), (1, 0), (0, 1), (1, 1), (2, 1), (3, 2)):
        nodes = grid_dag(k, ell)
        system = compile_dag(nodes, ["abAB"])
        values, costs = evaluate_dag(nodes, ["abAB"])
        d = symbolic_dag_assignment(system, nodes, values, {})
        check(all(r.xreplace(d) == 0 for r in system.residuals), "symbolic grid zero")
        if k+ell:
            check(len(system.variables) == 8*(k+ell)-4, "grid arity")
            check(len(system.residuals) == 8*(k+ell), "grid residual count")
        check(all(sp.Poly(r, *(system.parameters+system.variables)).total_degree() <= 2
                  for r in system.residuals), "grid degree")
        grid_symbolic += 1
    counts["grid_symbolic_systems"] = grid_symbolic

    # Mixed generic DAG: relator -> free conjugation -> inverse; reuse both branches.
    nodes = [Node("leaf", word="abAB"), Node("conjugate", (0,)),
             Node("inverse", (1,)), Node("product", (1, 2))]
    system = compile_dag(nodes, ["abAB"])
    check(len(system.variables) == 12 and len(system.residuals) == 13, "generic DAG counts")
    for _ in range(100):
        us = {1: evaluate_word("".join(rng.choice("aAbB") for _ in range(12)))}
        values, costs = evaluate_dag(nodes, ["abAB"], us)
        check(values[-1] == I, "inverse cancellation")
        d = symbolic_dag_assignment(system, nodes, values, us)
        check(all(r.xreplace(d) == 0 for r in system.residuals), "generic DAG zero")
    counts["generic_dag_symbolic_certificates"] = 100
    for bad in ([Node("leaf", word="a")],
                [Node("leaf", word="abAB"), Node("product", (0, 1))],
                [Node("leaf", word="abAB"), Node("leaf", word="")]):
        try:
            validate_dag(bad, ["abAB"])
        except ValueError:
            pass
        else:
            raise AssertionError("invalid DAG accepted")
    counts["invalid_dag_shapes_rejected"] = 3

    p, q = sp.symbols("p q", integer=True)
    ap, bq = sp.Matrix([[1, 2*p], [0, 1]]), sp.Matrix([[1, 0], [2*q, 1]])
    comm = ap*bq*ap.inv()*bq.inv()
    expected = sp.Matrix(2, 2, rectangular_matrix(p, q))
    check(all(sp.expand(x) == 0 for x in comm-expected), "symbolic rectangle identity")
    counts["symbolic_rectangle_identities"] = 1

    return {"status": "all checks passed", "seed": 20261002,
            "python": platform.python_version(), "sympy": sp.__version__,
            "scope": "exact arithmetic tests; not Lean/Rocq kernel verification; no claim of exhaustive mathematical proof by testing",
            "counts": counts}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    receipt = run()
    text = json.dumps(receipt, indent=2)+"\n"
    if args.receipt:
        args.receipt.write_text(text, encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
