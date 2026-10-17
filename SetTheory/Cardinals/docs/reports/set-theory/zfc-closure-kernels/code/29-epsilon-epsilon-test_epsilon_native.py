"""Finite diagnostics for the native epsilon proposal; no consistency claim.

Run from this directory: python test_epsilon_native.py
The final JSON separates logical controls from actual generated EPSC2 axioms.
"""

from __future__ import annotations

import json
from itertools import combinations, product
from pathlib import Path
import random
import time

from epsilon_native import (Arena, FiniteSemantics, Invalid, ResourceLimit,
                            accepts_bits, decode_candidate, decode_natural_candidate,
                            encode_candidate, gamma, pair, unpair)


HERE = Path(__file__).resolve().parent


def require_invalid(thunk):
    try:
        thunk()
    except Invalid:
        return
    raise AssertionError("invalid object was accepted")


def retained(a, roots):
    seen = set()
    stack = list(roots)
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        n = a.nodes[x]
        if n[0] not in ("b", "v"):
            stack.extend(n[1:])
    return sorted(seen)


def export_graph(a, roots):
    used = retained(a, roots.values())
    mapping = {old: new for new, old in enumerate(used)}
    nodes = []
    for old in used:
        n = a.nodes[old]
        nodes.append(list(n) if n[0] in ("b", "v")
                     else [n[0]] + [mapping[c] for c in n[1:]])
    return {"nodes": nodes, "roots": {k: mapping[v] for k, v in roots.items()}}


def run():
    start = time.monotonic()
    report = {"status": "finite diagnostics only; no binary table or consistency proof"}

    a = Arena()
    for n in range(20000):
        assert pair(*unpair(n)) == n
        assert a.natural_code(a.natural_formula(n)) == n
        assert a.natural_code(a.natural_term(n)) == n
    assert a.nodes[a.natural_formula(0)][0] == "b"
    assert a.nodes[a.natural_term(0)] == ("v", 0)
    assert a.nodes[a.natural_formula(1)][0] == "r"
    assert a.nodes[a.natural_term(1)][0] == "e"
    assert a.free(a.natural_formula(1)) == {0}
    assert not a.free(a.natural_term(1))
    report["typed_natural_roundtrips"] = 40000
    report["pair_roundtrips"] = 20000
    report["sort_collision_controls"] = 6

    # One shared arena allows exact syntax comparisons across operations.
    a = Arena()
    v = [a.var(i) for i in range(5)]
    bot, d0 = a.bot, a.eps(a.bot)
    open_choice = a.eps(a.rel(a.var(0), a.var(1)))
    nested_choice = a.eps(a.rel(a.eps(a.rel(a.var(0), a.var(2))), a.var(0)))
    roots = [v[0], v[1], d0, open_choice, nested_choice,
             a.rel(v[0], v[1]), a.rel(open_choice, v[1]),
             a.rel(nested_choice, v[0]),
             a.imp(a.rel(v[1], v[2]), a.rel(open_choice, v[0])),
             a.eps(a.imp(a.rel(a.var(1), a.var(0)), a.rel(a.var(0), a.var(2))))]
    terms = [d0, v[0], v[1], open_choice, nested_choice]
    substitutions = quantifiers = shifts = 0
    for graph in range(16):
        sem = FiniteSemantics(a, 2, graph)
        for env in product(range(2), repeat=3):
            for root in roots:
                for amount in (1, 2):
                    extra = (1,) * amount
                    assert sem.value(a.shift(root, amount), extra + env) == sem.value(root, env)
                    shifts += 1
                for label in range(3):
                    for term in terms:
                        env2 = list(env)
                        env2[label] = sem.value(term, env)
                        assert sem.value(a.substitute(root, label, term), env) == sem.value(root, tuple(env2))
                        substitutions += 1
                    if a.sort(root) == "f":
                        values = []
                        for x in range(2):
                            env2 = list(env)
                            env2[label] = x
                            values.append(bool(sem.value(root, tuple(env2))))
                        assert sem.value(a.exists_at(label, root), env) == any(values)
                        assert sem.value(a.forall_at(label, root), env) == all(values)
                        quantifiers += 2
        sem._value.cache_clear()
    report["capture_safe_substitution_semantics"] = substitutions
    report["free_index_shift_semantics"] = shifts
    report["epsilon_quantifier_macro_semantics"] = quantifiers

    # Closed bodies use nested epsilon terms and diagonal specializations.
    a = Arena()
    d0 = a.eps(a.bot)
    body0 = a.rel(a.var(0), d0)
    body1 = a.rel(a.var(0), a.var(0))
    body2 = a.rel(a.eps(a.rel(a.var(0), a.var(1))), a.var(0))
    bodies = [a.bot, body0, body1, body2, a.neg(body0), a.imp(body1, body2)]
    terms = [d0] + [a.eps(b) for b in bodies]
    critical_checks = 0
    for size, graphs in [(1, range(2)), (2, range(16)), (3, [0, 1, 73, 170, 341, 511])]:
        for graph in graphs:
            sem = FiniteSemantics(a, size, graph)
            for b in bodies:
                for t in terms:
                    f = a.critical(b, t)
                    assert not a.free(f)
                    assert sem.value(f, ())
                    critical_checks += 1
            sem._value.cache_clear()
    report["ground_critical_model_checks"] = critical_checks

    # A finite contradiction that genuinely needs a critical formula.
    e = a.eps(body0)
    P, Q = a.rel(d0, d0), a.rel(e, d0)
    critical = a.critical(body0, d0)
    assert not a.unsat([P, a.neg(Q)])
    assert not a.unsat([critical])
    assert a.unsat([P, a.neg(Q), critical])
    assert a.unsat([a.rel(d0, d0), a.neg(a.rel(a.eps(body1), a.eps(body1))),
                    a.critical(body1, d0)])
    report["generic_unsat_controls"] = {
        "critical_formula_required": True,
        "diagonal_specialization": True,
        "these_are_EPSC2_refutations": False,
    }
    graph = export_graph(a, {"assumption_P": P, "assumption_not_Q": a.neg(Q),
                             "critical_formula": critical})
    graph["status"] = "Generic logical diagnostic with external assumptions, not an EPSC2 certificate"
    (HERE / "generic_critical_unsat.json").write_text(json.dumps(graph, indent=2) + "\n")

    # Exhaustively compare the Boolean checker against direct clause semantics.
    atoms = [a.rel(d0, a.eps(b)) for b in (a.bot, body0, body1)]
    assert len(set(atoms)) == 3
    clauses = list(product((-1, 0, 1), repeat=3))
    clause_forms = []
    for c in clauses:
        f = a.bot
        for atom, sign in zip(atoms, c):
            if sign:
                f = a.disj(f, atom if sign == 1 else a.neg(atom))
        clause_forms.append(f)
    families = refutations = 0
    for count in range(4):
        for selection in combinations(range(27), count):
            expected = not any(all(any(sign and (value if sign == 1 else not value)
                                      for sign, value in zip(clauses[j], env))
                                   for j in selection)
                               for env in product((False, True), repeat=3))
            got = a.unsat([clause_forms[j] for j in selection])
            assert got == expected
            families += 1
            refutations += got
    report["boolean_clause_families"] = families
    report["boolean_unsat_families"] = refutations

    raw_forms = [a.bot, P, a.neg(P), a.imp(P, P), a.imp(P, a.bot)]
    raw_checks = 0
    for count in range(3):
        for family in product(raw_forms, repeat=count):
            assert a.unsat(family) == a.raw_index_unsat(family, max_index=4)
            raw_checks += 1
    report["raw_atom_mask_comparisons"] = raw_checks

    # Byte-free finite bit candidates: exact DAG framing and sorts.
    rng = random.Random(20261016)
    bit_roundtrips = 0
    for _ in range(500):
        matrices = rng.sample(bodies, rng.randrange(4))
        criticals = [(rng.choice(bodies), rng.choice(terms)) for _ in range(rng.randrange(4))]
        bits = encode_candidate(a, matrices, criticals)
        b, mm, cc = decode_candidate(bits)
        assert encode_candidate(b, mm, cc) == bits
        bit_roundtrips += 1
    report["binary_candidate_roundtrips"] = bit_roundtrips

    malformed = [gamma(1) + "111" + gamma(0) + gamma(0),
                 gamma(1) + "010" + gamma(0) + gamma(0) + gamma(0),
                 gamma(1) + "001" + gamma(0) + gamma(1) + gamma(0) + gamma(0),
                 gamma(1) + "000" + gamma(0) + gamma(1) + gamma(0) + gamma(0)]
    valid_critical_bits = encode_candidate(a, [], [(body2, d0)])
    malformed.extend([valid_critical_bits[:-1], valid_critical_bits + "0", "2"])
    assert all(not accepts_bits(s, max_atoms=12) for s in malformed)
    require_invalid(lambda: a.critical(a.rel(a.var(1), a.var(0)), d0))
    require_invalid(lambda: a.critical(body0, a.var(0)))
    require_invalid(lambda: a.epsc2(a.rel(a.var(4), d0)))
    require_invalid(lambda: a.epsc2(d0))
    require_invalid(lambda: a.ground_closure(a.rel(a.var(2), d0)))
    require_invalid(lambda: a.ground_closure(d0))
    report["invalid_candidate_controls"] = len(malformed) + 6
    # A caller-provided Bottom in the matrix list generates EPSC2(Bottom).
    # It must not become an assumed propositional Bottom.
    false_matrix_bits = encode_candidate(a, [a.bot], [])
    assert not accepts_bits(false_matrix_bits, max_atoms=12)
    assert not accepts_bits(valid_critical_bits, max_atoms=12)
    report["public_entrypoint_no_arbitrary_assumption"] = True
    (HERE / "native_false_matrix.bits").write_text(false_matrix_bits + "\n")
    (HERE / "nested_ground_critical.bits").write_text(valid_critical_bits + "\n")
    for code in range(200):
        _, _, _ = decode_natural_candidate(code)
    report["natural_candidate_decodes"] = 200

    # The native wrapper is checked against independently quantified loops.
    wrapper_metrics = []
    wrapper_checks = 0
    specs = ["false", "edge", "parameters", "mixed", "epsilon"]
    for kind in specs:
        a = Arena()
        x, y, p, q = [a.var(i) for i in range(4)]
        choices = {
            "false": a.bot,
            "edge": a.rel(x, y),
            "parameters": a.rel(p, q),
            "mixed": a.imp(a.rel(x, p), a.rel(y, q)),
            "epsilon": a.rel(a.eps(a.rel(a.var(0), a.var(3))), y),
        }
        matrix = choices[kind]
        before = len(a.nodes)
        axiom = a.epsc2(matrix)
        assert not a.free(axiom)
        for size, graphs in [(1, range(2)), (2, range(16)),
                             (3, [0, 1, 73, 170, 341, 511])]:
            for relation in graphs:
                sem = FiniteSemantics(a, size, relation)
                assert sem.value(axiom, ()) == sem.direct_epsc2(matrix)
                wrapper_checks += 1
                sem._value.cache_clear()
        used = retained(a, [axiom])

        def expanded(root, cache={}):
            # Reset below for each arena; counts expanded occurrences as an integer.
            if root not in cache:
                n = a.nodes[root]
                cache[root] = 1 if n[0] in ("b", "v") else 1 + sum(expanded(c, cache) for c in n[1:])
            return cache[root]

        metric = {"matrix": kind, "matrix_retained_nodes": len(retained(a, [matrix])),
                  "arena_nodes_before_wrapper": before,
                  "arena_nodes_after_wrapper": len(a.nodes),
                  "axiom_retained_nodes": len(used),
                  "expanded_axiom_nodes": expanded(axiom, {}),
                  "outer_boolean_atoms": len(a.propositional_atoms([axiom])),
                  "closed": True,
                  "unit": "syntactic nodes or Boolean atoms; never Turing-machine states"}
        wrapper_metrics.append(metric)
        if kind == "edge":
            out = export_graph(a, {"matrix": matrix, "generated_axiom": axiom})
            out["metrics"] = metric
            out["status"] = "Exact native EPSC2 instance for R(x,y), without critical formulas"
            (HERE / "native_epsc2_edge.json").write_text(json.dumps(out, indent=2) + "\n")
    report["native_wrapper_direct_semantics"] = wrapper_checks
    report["native_wrapper_metrics"] = wrapper_metrics

    # Recommended ground frontend: no outer p,q quantifiers. Ground terms
    # stand for the two illustrative parameter values, but all finite terms
    # are allowed in the actual schema enumerator.
    ground_metrics = []
    ground_checks = 0
    for kind in specs:
        a = Arena()
        x, y, p, q = [a.var(i) for i in range(4)]
        d0 = a.eps(a.bot)
        d1 = a.eps(a.rel(a.var(0), a.var(0)))
        choices = {
            "false": a.bot,
            "edge": a.rel(x, y),
            "parameters": a.rel(p, q),
            "mixed": a.imp(a.rel(x, p), a.rel(y, q)),
            "epsilon": a.rel(a.eps(a.rel(a.var(0), a.var(3))), y),
        }
        matrix = a.substitute(a.substitute(choices[kind], 2, d0), 3, d1)
        assert a.free(matrix) <= {0, 1}
        before = len(a.nodes)
        axiom = a.ground_closure(matrix)
        after = len(a.nodes)
        assert not a.free(axiom)
        # When outer parameter labels are unused, the four-slot wrapper is
        # literally the same closed epsilon syntax after canonical interning.
        assert axiom == a.epsc2(matrix)
        for size, graphs in [(1, range(2)), (2, range(16)),
                             (3, [0, 1, 73, 170, 341, 511])]:
            for relation in graphs:
                sem = FiniteSemantics(a, size, relation)
                assert sem.value(axiom, ()) == sem.direct_epsc2(matrix)
                ground_checks += 1
                sem._value.cache_clear()
        memo = {}

        def expanded_ground(root):
            if root not in memo:
                n = a.nodes[root]
                memo[root] = 1 if n[0] in ("b", "v") else 1 + sum(expanded_ground(c) for c in n[1:])
            return memo[root]

        metric = {"matrix": kind, "parameters_grounded_by": ["epsilon Bottom", "epsilon R(v0,v0)"],
                  "matrix_retained_nodes": len(retained(a, [matrix])),
                  "arena_nodes_before_wrapper": before,
                  "arena_nodes_after_wrapper": after,
                  "axiom_retained_nodes": len(retained(a, [axiom])),
                  "expanded_axiom_nodes": expanded_ground(axiom),
                  "outer_boolean_atoms": len(a.propositional_atoms([axiom])),
                  "closed": True,
                  "unit": "syntactic nodes or Boolean atoms; never Turing-machine states"}
        ground_metrics.append(metric)
        if kind in ("edge", "mixed"):
            out = export_graph(a, {"matrix": matrix, "generated_axiom": axiom})
            out["metrics"] = metric
            out["status"] = "Exact primary ground-closure axiom, without critical formulas"
            (HERE / f"native_ground_{kind}.json").write_text(json.dumps(out, indent=2) + "\n")
            bits = encode_candidate(a, [matrix], [])
            assert not accepts_bits(bits, max_atoms=12)
            (HERE / f"native_ground_{kind}.bits").write_text(bits + "\n")
    report["ground_wrapper_direct_semantics"] = ground_checks
    report["ground_wrapper_metrics"] = ground_metrics
    report["vacuous_outer_parameters_literal_identity"] = len(specs)
    report["elapsed_seconds"] = round(time.monotonic() - start, 3)
    (HERE / "epsilon_evidence.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    run()

