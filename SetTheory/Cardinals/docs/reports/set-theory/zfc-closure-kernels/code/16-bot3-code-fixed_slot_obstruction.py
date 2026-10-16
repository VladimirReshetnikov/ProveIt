#!/usr/bin/env python3
"""Independent Boolean counterinterpretation of the exact fixed-slot PSC emitter.

All_i is interpreted as identity; R(0,1) is true, all other indexed atoms false.
This is an algebraic proof-calculus counterinterpretation, not a Tarski model.
The template below is the curried adapter in psc_backend_experiment.py at
ProveIt96836f9eea3540e96322c3d28c7127a582aae223, with its k=c+2 discipline.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
from itertools import product
import json
from pathlib import Path


TOP = ("top",)
BOTTOM = ("bottom",)


def Hole(name): return ("hole", name)
def Rel(i, j): return ("rel", i, j)
def Imp(a, b): return ("imp", a, b)
def All(i, a): return ("all", i, a)
def Not(a): return Imp(a, BOTTOM)
def And(a, b): return Not(Imp(a, Not(b)))
def Or(a, b): return Imp(Not(a), b)
def Exists(i, a): return Not(All(i, Not(a)))
def Sub(x, y, z): return All(z, Imp(Rel(z, x), Rel(z, y)))


def psc_parts(phi, k):
    # Exact formula shape, including curried closedness and binder shadowing.
    bounded = All(0, Exists(k, All(1, Imp(phi, Sub(1, k, 0)))))
    guard = Or(Sub(0, 1, k), Rel(0, k))
    closed = All(0, Imp(guard, All(1, Imp(phi, Rel(1, k)))))
    support = All(1, Imp(Rel(1, k), Exists(0, phi)))
    axiom = Imp(bounded, All(1, Exists(k, And(closed, support))))
    return dict(bounded=bounded, guard=guard, closed=closed,
                support=support, axiom=axiom)


def value(f, holes=None):
    holes = {} if holes is None else holes
    tag = f[0]
    if tag == "top": return True
    if tag == "bottom": return False
    if tag == "hole": return holes[f[1]]
    if tag == "rel": return f[1] == 0 and f[2] == 1
    if tag == "imp": return not value(f[1], holes) or value(f[2], holes)
    if tag == "all": return value(f[2], holes)
    raise ValueError(f)


def rename_all_labels(f, permutation):
    if f[0] in ("top", "bottom", "hole"):
        return f
    if f[0] == "rel":
        return Rel(permutation.get(f[1], f[1]), permutation.get(f[2], f[2]))
    if f[0] == "imp":
        return Imp(rename_all_labels(f[1], permutation),
                   rename_all_labels(f[2], permutation))
    if f[0] == "all":
        return All(permutation.get(f[1], f[1]),
                   rename_all_labels(f[2], permutation))
    raise ValueError(f)


def rho8(a, b, c, u):
    # Exact Lukasiewicz row from the pinned upstream symbolic spec.
    return Imp(Imp(Imp(c, u), a), Imp(Imp(a, c), Imp(b, c)))


def check_emitter(path):
    """Compare to only the pure template function from the exact pinned bytes."""
    data = path.read_bytes()
    expected = "33337fc228b1347b7bb942bfdd98511e9d88da24458a9f0b759a5ed90f039902"
    digest = hashlib.sha256(data).hexdigest()
    if digest != expected:
        raise ValueError("Emitter source does not match the pinned source bytes")
    tree = ast.parse(data)
    functions = [f for f in tree.body if isinstance(f, ast.FunctionDef)
                 and f.name == "psc_template"]
    if len(functions) != 1:
        raise ValueError("Expected exactly one pure psc_template definition")
    coerce = lambda f: Hole("phi") if f == "c" else f
    namespace = {
        "All": lambda i, f: All(i, coerce(f)),
        "Imp": lambda f, g: Imp(coerce(f), coerce(g)),
        "Rel": Rel, "Or": Or, "And": And,
        "Ex": lambda i, f: Exists(i, coerce(f)),
    }
    # Only the hash-checked pure function is compiled. No emitter imports,
    # backend operations, filesystem calls, or main entrypoint are executed.
    exec(compile(ast.Module(body=functions, type_ignores=[]), str(path), "exec"),
         namespace)
    for k in (2, 3, 19):
        assert namespace["psc_template"](k) == psc_parts(Hole("phi"), k)["axiom"]
    return {"sha256": digest, "exact_template_AST_matches": 3}


def check():
    phi = Hole("phi")
    psc_cases = 0
    example_rows = []
    for k in range(2, 1002):
        formulas = psc_parts(phi, k)
        for p in (False, True):
            got = {name: value(f, {"phi": p}) for name, f in formulas.items()}
            assert got == dict(bounded=not p, guard=True, closed=not p,
                               support=True, axiom=True)
            psc_cases += 1
            if k == 2:
                example_rows.append(dict(phi=p, **got))

    # Independent checks of every retained logical row and the extra proposed
    # same-variable specialization / EFQ rows. These finite truth tables exhaust
    # Boolean payloads; the mathematical argument is uniform in binder labels.
    a, b, c, u = map(Hole, ("a", "b", "c", "u"))
    counts = dict(rho8=0, rho6=0, QI=0, commutation=0,
                  atomic_vacuity=0, same_variable_specialization=0,
                  EFQ=0, irreflexivity=0, GEN=0, MP=0)
    for bits in product((False, True), repeat=4):
        env = dict(zip(("a", "b", "c", "u"), bits))
        assert value(rho8(a, b, c, u), env)
        counts["rho8"] += 1
    for i, p in product(range(5), (False, True)):
        env = {"a": p}
        assert value(Imp(Exists(i, All(i, a)), a), env)
        counts["rho6"] += 1
        assert value(Imp(All(i, a), a), env)
        counts["same_variable_specialization"] += 1
        assert value(Imp(BOTTOM, a), env)
        counts["EFQ"] += 1
    for i, p, q in product(range(5), (False, True), (False, True)):
        assert value(Imp(All(i, Imp(a, b)), Imp(All(i, a), All(i, b))),
                     {"a": p, "b": q})
        counts["QI"] += 1
    for i, j, p in product(range(5), range(5), (False, True)):
        assert value(Imp(All(i, All(j, a)), All(j, All(i, a))), {"a": p})
        counts["commutation"] += 1
    for i, j, k in product(range(5), repeat=3):
        assert value(Imp(Rel(i, j), All(k, Rel(i, j))))
        counts["atomic_vacuity"] += 1
    for i in range(5):
        assert value(All(i, Not(Rel(i, i))))
        counts["irreflexivity"] += 1
        assert value(All(i, TOP))
        counts["GEN"] += 1
    for p, q in product((False, True), repeat=2):
        assert not (p and (not p or q)) or q
        counts["MP"] += 1

    fresh_instantiation = Imp(All(0, Rel(0, 1)), Rel(2, 1))
    identified_instantiation = Imp(All(0, Rel(0, 1)), Rel(1, 1))
    assert not value(fresh_instantiation)
    assert not value(identified_instantiation)

    # Scope control: a distinct, alpha-renamed version of the entire closed
    # Truth-matrix wrapper is NOT valid in this counterinterpretation.
    # For code c=0 the emitted fresh binder is k=2. Swap labels0 and3 everywhere.
    original_truth = psc_parts(TOP, 2)["axiom"]
    renamed_truth = rename_all_labels(original_truth, {0: 3, 3: 0})
    assert value(original_truth) and not value(renamed_truth)

    # Exact emitted low-code cases: code0 is Truth, code1 is Bottom.
    assert value(psc_parts(TOP, 2)["axiom"])
    assert value(psc_parts(BOTTOM, 3)["axiom"])

    return {
        "source_commit": "96836f9eea3540e96322c3d28c7127a582aae223",
        "quantifier_operation": "identity",
        "true_membership_atoms": [[0, 1]],
        "all_other_membership_atoms": False,
        "primitive_bottom": False,
        "truth": True,
        "exact_fixed_slot_PSC_cases": psc_cases,
        "k_range_tested": [2, 1001],
        "uniform_PSC_reduction": "SB=not(phi);guard=true;closed=not(phi);support=true;PSC=true",
        "truth_table": example_rows,
        "logical_row_cases": counts,
        "fresh_variable_instantiation_is_false": True,
        "variable_identification_instantiation_is_false": True,
        "low_code_cases_0_1_checked": True,
        "independently_alpha_renamed_wrapper_is_false": True,
        "ordinary_first_order_membership_model": False,
        "scope": "exact fixed-slot PSC skeleton plus same-variable UI and EFQ",
        "C_G_bundle_validity_claimed": False,
        "binary_machine_nonhalting_claimed": False,
    }


def main():
    if not __debug__:
        raise RuntimeError("Run without -O; this checker uses assertions")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--emitter", type=Path,
                        help="Optional pinned psc_backend_experiment.py for AST comparison")
    args = parser.parse_args()
    evidence = check()
    if args.emitter:
        evidence["pinned_emitter_comparison"] = check_emitter(args.emitter)
    text = json.dumps(evidence, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
