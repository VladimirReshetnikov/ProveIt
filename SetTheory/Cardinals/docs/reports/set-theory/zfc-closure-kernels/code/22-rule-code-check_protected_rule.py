"""Independent checks for the unary protected-witness EPSC inference.

Premise: all x exists b all y (beta(x,b,y;p) -> y subset b).
Output: EPSC hull for rho(x,y;p) = all b beta(x,b,y;p).
No finite structure is asserted to model all EPSC. The checks validate the
pure logical premise-to-bound implication and exact formula transport.
"""
from __future__ import annotations

import argparse
from itertools import product
import json
from pathlib import Path
import random

import debruijn_kernel as k
import check_wrapper_transport as w
from check_debruijn_kernel import naive_subst


def protected_hull_body(beta):
    # beta's root environment is [y,b,x,parameters]. Two insertions reserve
    # slots before substituting away y0 into position2. The new All binds b.
    zeta = k.subst0(k.edit(k.edit(beta, 3, 0), 3, 0), 2)
    return k.all_(zeta)


def protected_premise(beta):
    sub_y_b = k.all_(k.imp(k.rel(0, 1), k.rel(0, 2)))
    return k.all_(k.ex(k.all_(k.imp(beta, sub_y_b))))


def hull_from_body(body):
    eps_x = k.all_(k.neg(k.rel(0, 1)))
    step = k.all_(k.imp(w.or_(eps_x, k.rel(0, 2)), k.imp(body, k.rel(1, 2))))
    support = k.imp(k.rel(0, 1), k.ex(body))
    return k.ex(k.all_(w.and_(step, support)))


def independent_rho_ast(beta_ast):
    # The root rho environment is [x,y,params]; inside its All b it is
    # [b,x,y,params]. This independent AST map has no extra hull slot.
    zeta = w.rename_free(beta_ast, lambda i: (2, 0, 1)[i] if i < 3 else i)
    return ("all", zeta)


def direct_premise(beta_ast, domain, relation, params):
    def holds(x, b, y):
        return k.satisfies(beta_ast, domain, relation, (y, b, x) + params)
    def sub(y, b):
        return all((z, y) not in relation or (z, b) in relation for z in domain)
    return all(any(all(not holds(x, b, y) or sub(y, b)
                       for y in domain) for b in domain) for x in domain)


def run():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    structural = 0
    for beta in range(100000):
        ast = k.decode(beta)
        got = k.decode(protected_hull_body(beta))
        wanted = ("all", w.rename_free(
            ast, lambda i: (2, 0, 1)[i] if i < 3 else i + 1
        ))
        assert got == wanted
        structural += 1

    rng = random.Random(16002610)
    forms = [k.BOT] + [k.rel(i, j) for i in range(5) for j in range(5)]
    # Explicit nested binder cases accompany the deterministic random forms.
    forms += [k.all_(k.rel(1, 2)), k.all_(k.ex(k.rel(4, 0)))]
    for _ in range(32):
        a, b = rng.choice(forms), rng.choice(forms)
        forms.append(k.all_(a) if rng.randrange(3) == 0 else k.imp(a, b))

    dom = (0, 1)
    pairs = tuple(product(dom, repeat=2))
    semantic_transport = 0
    semantic_formulas = 0
    logical_implications = 0
    true_premises = 0
    for mask in range(16):
        relation = {p for bit, p in enumerate(pairs) if mask >> bit & 1}
        for beta in forms:
            beta_ast = k.decode(beta)
            rho_ast = independent_rho_ast(beta_ast)
            rho = k.encode(rho_ast)
            body = protected_hull_body(beta)
            premise = k.decode(protected_premise(beta))
            hull = k.decode(hull_from_body(body))
            _, _, expected_bound, expected_hull = w.wrapper_parts(rho)
            assert k.encode(hull) == expected_hull
            assert k.free_arity(hull) == max(0, k.free_arity(beta_ast) - 3)
            for params in product(dom, repeat=2):
                p = direct_premise(beta_ast, dom, relation, params)
                assert k.satisfies(premise, dom, relation, params) == p
                assert k.satisfies(hull, dom, relation, params) == w.intended_hull(
                    rho_ast, dom, relation, params
                )
                semantic_formulas += 2
                b = k.satisfies(k.decode(expected_bound), dom, relation, params)
                assert not p or b
                logical_implications += 1
                true_premises += p
                for x, y, v in product(dom, repeat=3):
                    assert k.satisfies(k.decode(body), dom, relation, (x, y, v) + params) == all(
                        k.satisfies(beta_ast, dom, relation, (y, witness, x) + params)
                        for witness in dom
                    )
                    semantic_transport += 1

    # Completeness adapter: beta=the ordinary bound matrix has no free b slot.
    # The protected rho is then equivalent to the source rho in nonempty FOL.
    adapter_checks = 0
    for rho in forms:
        _, beta, old_bound, _ = w.wrapper_parts(rho)
        assert protected_premise(beta) == old_bound
        source = k.decode(rho)
        protected = independent_rho_ast(k.decode(beta))
        for mask in range(16):
            relation = {p for bit, p in enumerate(pairs) if mask >> bit & 1}
            for env in product(dom, repeat=5):
                assert k.satisfies(source, dom, relation, env) == k.satisfies(
                    protected, dom, relation, env
                )
                adapter_checks += 1

    # Existential protection is unsound: over identity membership, each
    # beta-fiber y=b is bounded, but its union over b is not subset-bounded.
    identity_relation = {(0, 0), (1, 1)}
    beta = k.rel(0, 1)
    ast = k.decode(beta)
    assert direct_premise(ast, dom, identity_relation, ())
    body = independent_rho_ast(ast)[1]
    existential_rho = k.ex(k.encode(body))
    _, _, existential_bound, _ = w.wrapper_parts(existential_rho)
    assert not k.satisfies(k.decode(existential_bound), dom, identity_relation, ())

    # A binder-insensitive final substitution captures y into the inner z.
    beta = k.all_(k.rel(1, 2))
    padded = k.decode(k.edit(k.edit(beta, 3, 0), 3, 0))
    bad_body = ("all", naive_subst(padded, 2))
    good_body = k.decode(protected_hull_body(beta))
    row_one = {(1, 0), (1, 1)}
    assert k.satisfies(good_body, dom, row_one, (0, 1, 0))
    assert not k.satisfies(bad_body, dom, row_one, (0, 1, 0))

    # Dropping one reservation moves genuine parameters into the hull slot.
    beta = k.rel(3, 4)
    bad_one_insertion = k.all_(k.subst0(k.edit(beta, 3, 0), 2))
    assert bad_one_insertion != protected_hull_body(beta)

    return {
        "status": "PASS",
        "numeric_beta_codes": 100000,
        "independent_AST_transport_checks": structural,
        "independent_semantic_transport_checks": semantic_transport,
        "independent_semantic_premise_hull_checks": semantic_formulas,
        "premise_implies_protected_bound_cases": logical_implications,
        "premise_true_cases": true_premises,
        "ordinary_rule_adapter_semantic_checks": adapter_checks,
        "negative_controls": ["existential protection", "binder-insensitive substitution", "one missing insertion"],
        "hull_body": "All(subst0(edit(edit(beta,3,0),3,0),2))",
        "beta_root_slots": "[y,b,x,parameters]",
        "zeta_root_slots": "[b,x,y,v,parameters]",
        "new_unary_proof_production": "8*p+7, where p proves the parsed protected premise",
        "requires_b_freshness_check": False,
        "requires_arbitrary_runtime_remapper": False,
        "claims_all_finite_models_satisfy_EPSC": False,
        "claims_compiled_machine_or_state_bound": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(run(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(result)
    print(result, end="")
