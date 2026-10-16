"""Reproducible finite diagnostics for the de Bruijn Hilbert reference."""
from __future__ import annotations

import argparse
from itertools import product
import json
from pathlib import Path
import random

import debruijn_kernel as k


def naive_subst(a, j):
    """Intentionally wrong: does not protect bound slots while descending."""
    if a[0] == "bottom":
        return a
    if a[0] == "rel":
        f = lambda i: j if i == 0 else i - 1
        return ("rel", f(a[1]), f(a[2]))
    if a[0] == "imp":
        return ("imp", naive_subst(a[1], j), naive_subst(a[2], j))
    return ("all", naive_subst(a[1], j))


def identity_proof(a):
    x = k.proof_k(a, k.imp(a, a))
    y = k.proof_k(a, a)
    s = k.proof_s(a, k.imp(a, a), a)
    return k.proof_mp(y, k.proof_mp(x, s))


def run():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    counts = {}
    for n in range(100000):
        assert k.encode(k.decode(n)) == k.normalize(n)
        assert k.normalize(k.normalize(n)) == k.normalize(n)
        assert k.decode(k.encode(k.decode(n))) == k.decode(n)
        for j in range(3):
            assert k.normalize(k.subst0(n, j)) == k.subst0(n, j)
        assert k.normalize(k.lift(n)) == k.lift(n)
    assert k.BOT == 0 and k.imp(k.BOT, k.BOT) == 2
    assert k.decode(0) != k.decode(2)
    assert k.normalize(2) == 2
    counts["numeric_codes_bijective_roundtrip"] = 100000
    counts["primitive_bottom0_truth2_distinct"] = True

    # Syntax is generated independently of the numeric decoder. Recursive
    # witnesses include alternations of implication and nested quantifiers.
    rng = random.Random(20261016)
    atoms = [k.BOT] + [k.rel(i, j) for i in range(3) for j in range(3)]
    forms = list(atoms)
    for _ in range(110):
        a = rng.choice(forms)
        b = rng.choice(forms)
        forms.append(k.all_(a) if rng.randrange(3) == 0 else k.imp(a, b))
    # Complete two-point binary relations and assignments; the semantic
    # equalities themselves test genuine capture avoidance, not code identity.
    dom = (0, 1)
    pairs = tuple(product(dom, repeat=2))
    semantic = 0
    ui = 0
    for mask in range(16):
        relation = {p for bit, p in enumerate(pairs) if mask >> bit & 1}
        for a in forms:
            ast = k.decode(a)
            arity = max(3, k.free_arity(ast))
            for env in product(dom, repeat=arity):
                sa = k.satisfies(ast, dom, relation, env)
                for x in dom:
                    assert k.satisfies(k.decode(k.lift(a)), dom, relation, (x,) + env) == sa
                    semantic += 1
                for j in range(3):
                    assert k.satisfies(k.decode(k.subst0(a, j)), dom, relation, env) == k.satisfies(
                        ast, dom, relation, (env[j],) + env
                    )
                    semantic += 1
                    assert k.satisfies(k.decode(k.UI(a, j)), dom, relation, env)
                    ui += 1
    counts["independent_semantic_map_checks"] = semantic
    counts["UI_semantic_checks"] = ui

    ud = 0
    for mask in range(16):
        relation = {p for bit, p in enumerate(pairs) if mask >> bit & 1}
        for a, b in product(forms[:16], repeat=2):
            ast = k.decode(k.UD(a, b))
            for env in product(dom, repeat=max(3, k.free_arity(ast))):
                assert k.satisfies(ast, dom, relation, env)
                ud += 1
    counts["UD_semantic_checks"] = ud

    # Named reading of body: exists z. R(x,z). With inequality this is true
    # for every x, but the capture-corrupted instance exists z. R(z,z) is false.
    body = k.ex(k.rel(1, 0))
    inequality = {(0, 1), (1, 0)}
    good = k.decode(k.UI(body, 0))
    bad = ("imp", k.decode(k.all_(body)), naive_subst(k.decode(body), 0))
    assert k.satisfies(good, dom, inequality, (0, 0, 0))
    assert not k.satisfies(bad, dom, inequality, (0, 0, 0))

    # UD without lifting confuses the outer parameter with the new bound slot.
    a = k.rel(0, 0)
    bad_ud = k.imp(k.all_(k.imp(a, a)), k.imp(a, k.all_(a)))
    diag = {(0, 0)}
    assert k.satisfies(k.decode(k.UD(a, a)), dom, diag, (0, 0, 0))
    assert not k.satisfies(k.decode(bad_ud), dom, diag, (0, 0, 0))

    # The retired quantifier-only algebra cannot validate this kernel:
    # identity All and independent values R00=True, R11=False falsify UI.
    transport = k.UI(k.rel(0, 0), 1)
    assert k.decode(transport) == (
        "imp", ("all", ("rel", 0, 0)), ("rel", 1, 1)
    )
    counts["negative_controls_rejected"] = 3

    # Identity proof from K/S, constructed rather than treated as a theorem.
    a = k.rel(0, 1)
    x = k.proof_k(a, k.imp(a, a))
    y = k.proof_k(a, a)
    s = k.proof_s(a, k.imp(a, a), a)
    identity = identity_proof(a)
    check = k.checker()
    assert check(identity) == k.imp(a, a)
    assert check(k.proof_gen(identity)) == k.all_(k.imp(a, a))
    assert check(k.proof_ui(k.rel(0, 0), 1)) == transport
    assert check(k.proof_ud(a, k.rel(0, 0))) == k.UD(a, k.rel(0, 0))
    assert check(k.proof_mp(x, y)) is None
    assert check(k.proof_theory(0)) is None
    assert all(check(n) != k.BOT for n in range(5000))
    counts["proof_codes_scanned_no_refutation_claim"] = 5000

    # A genuine falsity connective needs ex-falso. Construct it from this
    # exact K/S/C basis, rather than merely calling the constant "Bottom".
    bottom_identity = identity_proof(k.BOT)
    premise = k.proof_mp(
        bottom_identity, k.proof_k(k.imp(k.BOT, k.BOT), k.neg(a))
    )
    explosion = k.proof_mp(premise, k.proof_c(a, k.BOT))
    assert check(explosion) == k.imp(k.BOT, a)
    counts["explosion_certificate_verified"] = True

    # A closed inconsistent theory closes by MP. A malformed MP remains a
    # rejected certificate. The theory emitter, not the proof, owns axiom data.
    p = k.all_(k.rel(0, 0))
    theory = (p, k.neg(p))
    assert all(k.free_arity(k.decode(t)) == 0 for t in theory)
    tc = k.checker(lambda i: theory[i] if i < len(theory) else None)
    contradiction = k.proof_mp(k.proof_theory(0), k.proof_theory(1))
    assert tc(contradiction) == k.BOT
    assert tc(k.proof_mp(k.proof_theory(1), k.proof_theory(0))) is None
    counts["finite_theory_MP_refutation_code"] = contradiction
    counts["primitive_falsity_control"] = k.checker(lambda i: k.BOT if i == 0 else None)(7) == k.BOT

    return {
        "status": "PASS",
        "counts": counts,
        "shared_transform": "edit(code, depth, target): target=0 lift; target=j+1 subst0",
        "logic": "K/S/full classical contraposition; UI; UD; MP; theorem-only GEN",
        "closed_theory_emitter_required": True,
        "runtime_freshness_or_free_variable_predicate": False,
        "primitive_formula_constructors": 4,
        "positive_constructor_tags": 3,
        "formula_codec": "Bottom0; Rel(i,j)=1+3pair(i,j); Imp(a,b)=2+3pair(a,b); All(a)=3+3a",
        "formula_codec_aliases_or_collapses": False,
        "quantifier_payloads": 1,
        "proof_search_demonstrates_consistency": False,
        "PSC_EPSC_emitter_implemented": False,
        "Turing_machine_or_state_bound_claimed": False,
        "formal_proof_assistant_check_claimed": False,
        "counterexamples": {
            "capture": "All x Exists z R(x,z) does not imply Exists z R(z,z)",
            "missing_lift": "All x(P(x)->P(x)) does not imply P(y)->All x P(x)",
            "cross_variable": "UI emits All(Rel(0,0))->Rel(1,1), refuting independent atomic sorts",
        },
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(run(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(result)
    print(result, end="")
