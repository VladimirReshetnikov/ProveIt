#!/usr/bin/env python3
"""Equality-free EPSC1, with fixed DP or Binary Union repairs.

This is an exact formula generator and finite semantic cross-check, not a
proof-search engine, schema-satisfaction decision procedure, or TM compiler.
Its primitive AST has Bottom, membership, implication, and named universal
quantification. The preferred repair is exact Binary Union (BU); the exact
incoming-profile Pairing sentence (DP) and fixed two-parameter gate are
retained for comparison.
"""
from __future__ import annotations

import argparse
from collections import Counter
import itertools
import json
from pathlib import Path


def B(): return ("bottom",)
def M(x, y): return ("mem", x, y)
def I(a, b): return ("imp", a, b)
def A(x, f): return ("all", x, f)
def N(f): return I(f, B())
def C(a, b): return N(I(a, N(b)))
def O(a, b): return I(N(a), b)
def X(x, f): return N(A(x, N(f)))
def F(a, b): return C(I(a, b), I(b, a))
def Delta(x, y, z): return A(z, F(M(z, x), M(z, y)))
def Sub(x, y, z): return A(z, I(M(z, x), M(z, y)))
def Empty(x, z): return A(z, N(M(z, x)))


def check(f):
    if not isinstance(f, tuple) or not f:
        raise ValueError("Formula must be a nonempty tuple")
    tag = f[0]
    if tag == "bottom" and len(f) == 1:
        return
    if tag == "mem" and len(f) == 3:
        if any(type(v) is not int or v < 0 for v in f[1:]):
            raise ValueError("Variable labels must be nonnegative integers")
        return
    if tag == "imp" and len(f) == 3:
        check(f[1]); check(f[2]); return
    if tag == "all" and len(f) == 3:
        if type(f[1]) is not int or f[1] < 0:
            raise ValueError("Binder label must be a nonnegative integer")
        check(f[2]); return
    raise ValueError("Unsupported formula constructor or arity")


def variables(f):
    if f[0] == "bottom": return set()
    if f[0] == "mem": return set(f[1:])
    if f[0] == "imp": return variables(f[1]) | variables(f[2])
    return {f[1]} | variables(f[2])


def free(f):
    if f[0] == "bottom": return set()
    if f[0] == "mem": return set(f[1:])
    if f[0] == "imp": return free(f[1]) | free(f[2])
    return free(f[2]) - {f[1]}


def nodes(f):
    if f[0] in ("bottom", "mem"): return 1
    if f[0] == "all": return 1 + nodes(f[2])
    return 1 + nodes(f[1]) + nodes(f[2])


def subformulas(f):
    seen = set()
    def visit(t):
        if t in seen: return
        seen.add(t)
        if t[0] == "all": visit(t[2])
        if t[0] == "imp": visit(t[1]); visit(t[2])
    visit(f)
    return seen


def dag_nodes(f):
    return len(subformulas(f))


def metrics(f):
    tree_counts = Counter()
    def visit(t):
        tree_counts[t[0]] += 1
        if t[0] == "all": visit(t[2])
        if t[0] == "imp": visit(t[1]); visit(t[2])
    visit(f)
    return {
        "tree_nodes": nodes(f),
        "exact_named_dag_nodes": dag_nodes(f),
        "tree_constructor_counts": dict(sorted(tree_counts.items())),
        "dag_constructor_counts": dict(sorted(Counter(
            t[0] for t in subformulas(f)).items())),
    }


def pairing(start=0):
    """DP: exact pair of incoming-profile classes, with fresh local binders."""
    a, b, c, y, z0, z1 = range(start, start + 6)
    return A(a, A(b, X(c, A(y, F(M(y, c),
        O(Delta(y, a, z0), Delta(y, b, z1)))))))


def binary_union(start=0):
    """BU: forall A B exists C forall y, y in C iff (y in A or y in B)."""
    a, b, c, y = range(start, start + 4)
    return A(a, A(b, X(c, A(y, F(M(y, c), O(M(y, a), M(y, b)))))))


REPAIRS = {"dp": pairing, "bu": binary_union}


def epsc_wrapper(rho, parameter_slots=(2,), repair=None):
    """Generate universal EPSC closure, optionally fusing a CLOSED repair.

    x=0 and y=1 are the two matrix roles. Wrapper helpers are fresh for all
    matrix variables, including bound variables; repair binders are also
    fresh for both the matrix and wrapper. This helper supports a fixed
    two-parameter gate, but instance() exposes only the general unary schema.
    """
    check(rho)
    if (len(set(parameter_slots)) != len(parameter_slots) or
        any(type(v) is not int or v < 2 for v in parameter_slots)):
        raise ValueError("Parameter slots must be distinct integer labels >= 2")
    if not free(rho) <= {0, 1} | set(parameter_slots):
        raise ValueError("Matrix has a free variable outside its interface")
    if repair not in (None, "dp", "bu"):
        raise ValueError("Repair must be None, dp, or bu")
    first = max(variables(rho) | {0, 1} | set(parameter_slots)) + 1
    b, c, z = first, first + 1, first + 2
    bounded = A(0, X(b, A(1, I(rho, Sub(1, b, z)))))
    active = O(Empty(0, z), M(0, c))
    closed = A(0, A(1, I(C(active, rho), M(1, c))))
    supported = A(1, I(M(1, c), X(0, rho)))
    hull = X(c, C(closed, supported))
    conclusion = C(REPAIRS[repair](first + 3), hull) if repair else hull
    result = I(bounded, conclusion)
    for p in reversed(parameter_slots):
        result = A(p, result)
    check(result)
    if free(result):
        raise ValueError("Generated axiom is not a sentence")
    return result


def instance(rho, fused=None):
    """General EPSC1 instance; fused='dp' and fused='bu' are the two repairs.

    The earlier boolean fused=True spelling is retained as an alias for DP.
    """
    if fused is True: fused = "dp"
    if fused is False: fused = None
    return epsc_wrapper(rho, (2,), fused)


def fixed_gate_matrix():
    """Theta(x,y;a,b), where the two fixed parameter roles are 2 and 3."""
    empty_x = Empty(0, 4)
    return O(C(empty_x, Delta(1, 2, 5)),
             C(N(empty_x), Delta(1, 3, 6)))


def fixed_gate():
    return epsc_wrapper(fixed_gate_matrix(), (2, 3))


def evaluate(f, relation, env):
    """relation[y] is the bit mask of the members of domain object y."""
    tag = f[0]
    if tag == "bottom": return False
    if tag == "mem": return bool((relation[env[f[2]]] >> env[f[1]]) & 1)
    if tag == "imp": return not evaluate(f[1], relation, env) or evaluate(f[2], relation, env)
    for value in range(len(relation)):
        next_env = dict(env); next_env[f[1]] = value
        if not evaluate(f[2], relation, next_env): return False
    return True


def direct_eps_profile(rho, relation, parameter_slots=(2,)):
    """Independent set-of-bits semantics of LB and supported closure.

    Cases with false LB must not force a fused repair. In particular one
    fused instance is generally weaker than Repair AND that EPSC instance.
    """
    size = len(relation)
    cases = []
    for assignment in itertools.product(range(size), repeat=len(parameter_slots)):
        parameters = dict(zip(parameter_slots, assignment))
        outputs = [sum(1 << y for y in range(size)
                       if evaluate(rho, relation, parameters | {0: x, 1: y}))
                   for x in range(size)]
        bounded = all(any(all(not (outputs[x] >> y) & 1 or
                              relation[y] & ~relation[b] == 0
                              for y in range(size))
                          for b in range(size))
                      for x in range(size))
        output_union = 0
        for row in outputs: output_union |= row
        found = False
        for members in relation:
            if members & ~output_union: continue
            if all((relation[x] != 0 and not (members >> x) & 1) or
                   outputs[x] & ~members == 0 for x in range(size)):
                found = True; break
        cases.append({"parameters": list(assignment),
                      "locally_bounded": bounded, "supported_hull": found})
    return cases


def direct_eps(cases, repair=True):
    return all(not case["locally_bounded"] or
               (repair and case["supported_hull"]) for case in cases)


def direct_pairing(relation):
    return all(any(members == sum(1 << y for y in range(len(relation))
                    if relation[y] == relation[a] or relation[y] == relation[b])
                   for members in relation)
               for a in range(len(relation)) for b in range(len(relation)))


def direct_binary_union(relation):
    return all((a | b) in relation for a in relation for b in relation)


def run():
    matrices = {
        "false": B(),
        "membership": M(1, 2),
        "incoming_profile": Delta(1, 2, 9),
        "shadowing_control": A(2, I(M(0, 2), A(12, M(12, 1)))),
    }
    axioms = {name: {"matrix": rho, "epsc1": instance(rho),
                     "fused_dp": instance(rho, "dp"),
                     "fused_bu": instance(rho, "bu")}
              for name, rho in matrices.items()}
    fixed = {"dp": pairing(), "bu": binary_union(),
             "theta_matrix": fixed_gate_matrix(), "epsc_theta": fixed_gate()}
    for name, formula in fixed.items():
        check(formula)
        if name != "theta_matrix" and free(formula):
            raise ValueError("Fixed axiom is not closed")
    semantic_comparisons = 0
    fixed_comparisons = 0
    structures = 0
    truth_counts = {}
    disagreement_witnesses = {}
    vacuity_witnesses = {}
    for size in range(1, 4):
        counts = Counter(structures=0, dp=0, bu=0, epsc_theta=0,
                         dp_ne_bu=0, dp_ne_epsc_theta=0,
                         false_and_profile_instances=0)
        for bits in range(1 << (size * size)):
            relation = [(bits >> (size * y)) & ((1 << size) - 1)
                        for y in range(size)]
            dp = direct_pairing(relation)
            bu = direct_binary_union(relation)
            theta_cases = direct_eps_profile(fixed["theta_matrix"], relation, (2, 3))
            if not all(case["locally_bounded"] for case in theta_cases):
                raise ValueError("The disjoint fixed gate must be locally bounded")
            theta = direct_eps(theta_cases)
            for key, expected in (("dp", dp), ("bu", bu), ("epsc_theta", theta)):
                if evaluate(fixed[key], relation, {}) != expected:
                    raise ValueError("Fixed axiom disagrees with direct semantics: " + key)
                fixed_comparisons += 1
                counts[key] += expected
            if dp != bu:
                counts["dp_ne_bu"] += 1
                disagreement_witnesses.setdefault("dp_ne_bu", {
                    "size": size, "member_masks": relation, "dp": dp, "bu": bu})
            if dp != theta:
                counts["dp_ne_epsc_theta"] += 1
                disagreement_witnesses.setdefault("dp_ne_epsc_theta", {
                    "size": size, "member_masks": relation,
                    "dp": dp, "epsc_theta": theta})
            structures += 1
            counts["structures"] += 1
            ordinary = {}
            for name, rho in matrices.items():
                cases = direct_eps_profile(rho, relation)
                expected = direct_eps(cases)
                ordinary[name] = expected
                for key, repair in (("epsc1", True), ("fused_dp", dp), ("fused_bu", bu)):
                    actual = evaluate(axioms[name][key], relation, {})
                    if actual != direct_eps(cases, repair):
                        raise ValueError("Generated axiom disagrees with direct semantics: " + name + "/" + key)
                    semantic_comparisons += 1
                    if key != "epsc1" and actual != (repair and expected):
                        if any(case["locally_bounded"] for case in cases):
                            raise ValueError("Unexpected cause of fused-instance vacuity")
                        vacuity_witnesses.setdefault(key, {
                            "size": size, "member_masks": relation,
                            "matrix": name, "repair": repair,
                            "ordinary_instance": expected, "fused_instance": actual,
                            "all_parameter_premises_false": True})
                if name == "false":
                    # False has a logically valid LB premise, so its fused
                    # instances DO force the repair and an empty object.
                    if not all(case["locally_bounded"] for case in cases):
                        raise ValueError("False matrix must be locally bounded")
                    if expected != (0 in relation):
                        raise ValueError("False EPSC must assert existence of an empty object")
            counts["false_and_profile_instances"] += (
                ordinary["false"] and ordinary["incoming_profile"])
        truth_counts[str(size)] = dict(counts)
    if set(vacuity_witnesses) != {"fused_dp", "fused_bu"}:
        raise ValueError("Expected both fused variants to exhibit guarded vacuity")
    rejected = 0
    for bad in [M(1, 3), ("eq", 0, 1), ("all", -1, M(0, 1)),
                ("mem", True, 1), ("imp", B()), ["bottom"]]:
        try: instance(bad)
        except ValueError: rejected += 1
        else: raise ValueError("Invalid matrix accepted")
    fixed_metrics = {name: metrics(formula) for name, formula in fixed.items()}
    return {
        "status": "passed",
        "language": ["bottom", "membership", "implication", "forall"],
        "preferred_repair": "bu",
        "matrix_free_slots": {"x": 0, "y": 1, "p": 2},
        "fixed_gate_parameter_slots": {"a": 2, "b": 3},
        "bound_variables_unrestricted": True,
        "wrapper_and_repair_binders_fresh_for_matrix": True,
        "fixed_formulas": fixed,
        "fixed_formula_metrics": fixed_metrics,
        "repair_tree_node_saving_dp_to_bu": nodes(fixed["dp"]) - nodes(fixed["bu"]),
        "repair_named_dag_node_saving_dp_to_bu": dag_nodes(fixed["dp"]) - dag_nodes(fixed["bu"]),
        "instances": {name: dict(data, metrics={
            key: metrics(data[key]) for key in ("epsc1", "fused_dp", "fused_bu")})
            for name, data in axioms.items()},
        "checked_structures": structures,
        "schema_semantic_comparisons": semantic_comparisons,
        "fixed_axiom_semantic_comparisons": fixed_comparisons,
        "finite_truth_counts": truth_counts,
        "bare_fixed_axiom_disagreement_witnesses": disagreement_witnesses,
        "fused_instance_vacuity_witnesses": vacuity_witnesses,
        "malformed_matrix_rejections": rejected,
        "metric_scope": (
            "Primitive AST constructor nodes; variable labels stored inside mem/all nodes, "
            "with label magnitudes and encoding costs uncharged. DAG shares only identical "
            "named subformulas, not alpha-equivalent formulas. NOT machine states, register "
            "instructions, program bits, or compiled costs."),
        "semantic_scope": (
            "All 530 labeled nonempty membership structures of sizes 1..3. Direct bit-mask "
            "semantics are compared to the fixed DP, BU and EPSC[Theta] formulas, and to "
            "four ordinary/unary fused instances. This validates those formula encodings "
            "and the LB guard, not full-schema satisfaction or the repair-equivalence theorem. "
            "DP, BU and EPSC[Theta] are not asserted logically equivalent without EPSC1."),
        "finite_model_of_full_schema_claimed": False,
        "proof_search_engine_implemented": False,
        "binary_machine_compiled": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: result[key] for key in (
        "status", "checked_structures", "schema_semantic_comparisons",
        "fixed_axiom_semantic_comparisons", "fixed_formula_metrics")}))


if __name__ == "__main__":
    main()
