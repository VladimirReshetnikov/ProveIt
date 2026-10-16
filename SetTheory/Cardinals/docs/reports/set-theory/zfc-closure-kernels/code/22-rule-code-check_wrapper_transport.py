"""Independent checks of EPSC wrapper transport by the shared index edit.

This does not assert EPSC validity in arbitrary finite structures. It compares
the generated formulas to their intended quantified semantics in each model.
"""
from __future__ import annotations

import argparse
from itertools import product
import json
from pathlib import Path
import random

import debruijn_kernel as k


def rename_free(a, f, depth=0):
    """Independent AST-level free-index map, unused by generated wrappers."""
    if a[0] == "bottom":
        return a
    if a[0] == "rel":
        g = lambda i: i if i < depth else depth + f(i - depth)
        return ("rel", g(a[1]), g(a[2]))
    if a[0] == "imp":
        return ("imp", rename_free(a[1], f, depth), rename_free(a[2], f, depth))
    return ("all", rename_free(a[1], f, depth + 1))


def labels(a):
    if a[0] == "bottom":
        return ()
    if a[0] == "rel":
        return (a[1], a[2])
    if a[0] == "imp":
        return labels(a[1]) + labels(a[2])
    return labels(a[1])


def and_(a, b):
    return k.neg(k.imp(a, k.neg(b)))


def or_(a, b):
    return k.imp(k.neg(a), b)


def wrapper_parts(rho):
    """Only calls edit/subst0 for all formula transport, never rename_free."""
    h = k.edit(rho, 2, 0)  # x,y,v,params
    b = k.edit(k.subst0(h, 1), 1, 0)  # y,b,x,params

    eps_x = k.all_(k.neg(k.rel(0, 1)))  # z,x,y,v,params inside All
    left = k.all_(k.imp(or_(eps_x, k.rel(0, 2)), k.imp(h, k.rel(1, 2))))
    right = k.imp(k.rel(0, 1), k.ex(h))
    hull = k.ex(k.all_(and_(left, right)))

    subset_y_b = k.all_(k.imp(k.rel(0, 1), k.rel(0, 2)))
    bound = k.all_(k.ex(k.all_(k.imp(b, subset_y_b))))
    return h, b, bound, hull


def intended_bound(ast, domain, relation, params):
    def holds(x, y):
        return k.satisfies(ast, domain, relation, (x, y) + params)
    return all(any(all(not holds(x, y) or all(
        (z, y) not in relation or (z, b) in relation for z in domain
    ) for y in domain) for b in domain) for x in domain)


def intended_hull(ast, domain, relation, params):
    def holds(x, y):
        return k.satisfies(ast, domain, relation, (x, y) + params)
    def empty(x):
        return all((z, x) not in relation for z in domain)
    return any(
        all(not (empty(x) or (x, v) in relation) or all(
            not holds(x, y) or (y, v) in relation for y in domain
        ) for x in domain)
        and all((y, v) not in relation or any(holds(x, y) for x in domain)
                for y in domain)
        for v in domain
    )


def run():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    transport = 0
    for n in range(100000):
        ast = k.decode(n)
        assert all(i < n for i in labels(ast))
        assert k.free_arity(ast) <= n
        h = k.edit(n, 2, 0)
        b = k.edit(k.subst0(h, 1), 1, 0)
        assert k.decode(h) == rename_free(ast, lambda i: i if i < 2 else i + 1)
        assert k.decode(b) == rename_free(ast, lambda i: 2 if i == 0 else 0 if i == 1 else i + 1)
        transport += 2

    rng = random.Random(16102026)
    forms = [k.BOT] + [k.rel(i, j) for i in range(4) for j in range(4)]
    for _ in range(43):
        a, b = rng.choice(forms), rng.choice(forms)
        forms.append(k.all_(a) if rng.randrange(3) == 0 else k.imp(a, b))
    dom = (0, 1)
    pairs = tuple(product(dom, repeat=2))
    semantic_transports = 0
    semantic_wrappers = 0
    for mask in range(16):
        relation = {p for bit, p in enumerate(pairs) if mask >> bit & 1}
        for rho in forms:
            ast = k.decode(rho)
            h, b, bound, hull = wrapper_parts(rho)
            h, b, bound, hull = map(k.decode, (h, b, bound, hull))
            expected_arity = max(0, k.free_arity(ast) - 2)
            assert k.free_arity(bound) == expected_arity
            assert k.free_arity(hull) == expected_arity
            for params in product(dom, repeat=2):
                assert k.satisfies(bound, dom, relation, params) == intended_bound(ast, dom, relation, params)
                assert k.satisfies(hull, dom, relation, params) == intended_hull(ast, dom, relation, params)
                semantic_wrappers += 2
                for x, y, v in product(dom, repeat=3):
                    truth = k.satisfies(ast, dom, relation, (x, y) + params)
                    assert k.satisfies(h, dom, relation, (x, y, v) + params) == truth
                    assert k.satisfies(b, dom, relation, (y, v, x) + params) == truth
                    semantic_transports += 2

    # Primitive closure counter example. For arbitrary n the label lemma
    # proves correctness; these bounded examples exercise the constructor.
    for rho in range(50):
        _, _, b, h = wrapper_parts(rho)
        for _ in range(rho):
            b, h = k.all_(b), k.all_(h)
        assert k.free_arity(k.decode(b)) == 0
        assert k.free_arity(k.decode(h)) == 0

    return {
        "status": "PASS",
        "numeric_matrices": 100000,
        "independent_AST_transport_checks": transport,
        "independent_semantic_transport_checks": semantic_transports,
        "independent_semantic_wrapper_checks": semantic_wrappers,
        "raw_label_below_code_and_free_arity_bound_checks": 100000,
        "whole_wrapper_closure_examples_k_equals_code": 50,
        "hull_matrix": "edit(rho,2,0)",
        "bound_matrix": "edit(subst0(hull_matrix,1),1,0)",
        "requires_arbitrary_runtime_renaming": False,
        "closure_without_arity_scan": "Apply All exactly rho_code times to B or H",
        "claims_EPSC_valid_in_arbitrary_finite_models": False,
        "claims_machine_or_state_bound": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(run(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(result)
    print(result, end="")
