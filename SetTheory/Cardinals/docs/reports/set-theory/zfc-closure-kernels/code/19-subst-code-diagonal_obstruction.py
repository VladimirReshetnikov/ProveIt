"""Finite checks for two logical obstructions; no Turing-machine claim.

The proof, which applies to arbitrary formulas, is in theory_support.tex.
This file independently checks the small algebraic witnesses and finite
instances of their stated invariances. Python 3.10+, standard library only.
"""
from __future__ import annotations

import itertools
import json
from functools import lru_cache


def B(): return ("bot",)
def R(i, j): return ("rel", i, j)
def I(p, q): return ("imp", p, q)
def Q(i, p): return ("all", i, p)
def N(p): return I(p, B())
def E(i, p): return N(Q(i, N(p)))
def And(p, q): return N(I(p, N(q)))
def Or(p, q): return I(N(p), q)
def Iff(p, q): return And(I(p, q), I(q, p))


@lru_cache(None)
def evaluate(p, env):
    """Coordinate semantics with a deliberately anomalous diagonal."""
    tag = p[0]
    if tag == "bot": return False
    if tag == "rel":
        _, i, j = p
        return i != j and env[i] == env[j]
    if tag == "imp":
        return not evaluate(p[1], env) or evaluate(p[2], env)
    _, i, body = p
    return all(evaluate(body, env[:i] + (bit,) + env[i+1:])
               for bit in (0, 1))


def rename_free(p, source, target):
    """Tests call this only when capture is impossible."""
    tag = p[0]
    if tag == "bot": return p
    if tag == "rel":
        return R(*(target if i == source else i for i in p[1:]))
    if tag == "all":
        return p if p[1] == source else Q(p[1], rename_free(p[2], source, target))
    return I(rename_free(p[1], source, target), rename_free(p[2], source, target))


def rename_all(p, permutation):
    if p[0] == "bot": return p
    if p[0] == "rel": return R(*(permutation[i] for i in p[1:]))
    if p[0] == "all": return Q(permutation[p[1]], rename_all(p[2], permutation))
    return I(rename_all(p[1], permutation), rename_all(p[2], permutation))


def identity_semantics(p):
    """Simpler actual fixed-slot PSC model: Q is identity, only R(0,1) true."""
    tag = p[0]
    if tag == "bot": return False
    if tag == "rel": return p[1:] == (0, 1)
    if tag == "all": return identity_semantics(p[2])
    if tag == "payload": return p[1]
    return not identity_semantics(p[1]) or identity_semantics(p[2])


def psc(p, k):
    sub = lambda x, y, z: Q(z, I(R(z, x), R(z, y)))
    sb = Q(0, E(k, Q(1, I(p, sub(1, k, 0)))))
    guard = Or(sub(0, 1, k), R(0, k))
    closed = Q(0, I(guard, Q(1, I(p, R(1, k)))))
    support = Q(1, I(R(1, k), E(0, p)))
    return sb, Q(1, E(k, And(closed, support)))


def run():
    # The actual code+2 PSC wrapper remains true even after specialization.
    psc_cases = 0
    for k, truth in itertools.product(range(2, 102), (False, True)):
        premise, conclusion = psc(("payload", truth), k)
        assert identity_semantics(premise) == (not truth)
        assert identity_semantics(conclusion) == (not truth)
        assert identity_semantics(I(premise, conclusion))
        psc_cases += 1
    assert not identity_semantics(I(Q(0, R(0, 1)), R(2, 1)))

    # Every instance of positive and negative ATOMIC instantiation in this
    # four-label slice is valid, including diagonal targets.
    envs = tuple(itertools.product((0, 1), repeat=4))
    atoms = tuple(R(i, j) for i, j in itertools.product(range(4), repeat=2))
    atomic_ui_cases = 0
    for atom, negate, x, y in itertools.product(atoms, (False, True), range(4), range(4)):
        p = N(atom) if negate else atom
        instance = I(Q(x, p), rename_free(p, x, y))
        for env in envs:
            assert evaluate(instance, env)
            atomic_ui_cases += 1

    # Finite composite controls, using labels 0/1/2 and fresh target 3.
    base = [B()] + [R(i, j) for i, j in itertools.product(range(3), repeat=2)]
    forms = base + [N(p) for p in base]
    forms += [I(p, q) for p, q in itertools.product(base, repeat=2)]
    forms += [Q(i, p) for i, p in itertools.product(range(3), base)]
    forms += [Q(0, I(p, Q(1, q))) for p, q in itertools.product(base, repeat=2)]
    fresh_ui_cases = alpha_cases = modal_cases = permutation_cases = 0
    permutation = (2, 0, 1, 3)
    for p in forms:
        for x in range(3):
            fresh_ui = I(Q(x, p), rename_free(p, x, 3))
            alpha_left, alpha_right = Q(x, p), Q(3, rename_free(p, x, 3))
            laws = (
                I(Q(x, p), p),
                I(Q(x, p), Q(x, Q(x, p))),
                I(N(Q(x, p)), Q(x, N(Q(x, p)))),
                I(E(x, Q(x, p)), p),
                I(p, Q(x, E(x, p))),
                I(Q(x, Q((x+1) % 3, p)), Q((x+1) % 3, Q(x, p))),
            )
            for env in envs:
                assert evaluate(fresh_ui, env)
                assert evaluate(alpha_left, env) == evaluate(alpha_right, env)
                fresh_ui_cases += 1
                alpha_cases += 1
                for law in laws:
                    assert evaluate(law, env)
                    modal_cases += 1
        renamed = rename_all(p, permutation)
        for env in envs:
            transformed = tuple(env[permutation[i]] for i in range(4))
            assert evaluate(renamed, env) == evaluate(p, transformed)
            permutation_cases += 1

    # The necessary collision law is still false, at every assignment.
    matrix = Iff(Iff(R(0, 1), R(0, 2)), R(1, 2))
    instance = I(Q(0, matrix), rename_free(matrix, 0, 1))
    counterexample_rows = []
    for env in itertools.product((0, 1), repeat=3):
        before = evaluate(Q(0, matrix), env)
        after = evaluate(rename_free(matrix, 0, 1), env)
        assert before and not after and not evaluate(instance, env)
        counterexample_rows.append({"assignment": list(env), "universal": before,
                                    "colliding_instance": after})
    return {
        "scope": "Logical counterinterpretations, not ordinary one-relation models or TM theorems",
        "actual_fixed_slot_psc_identity_cases": psc_cases,
        "positive_and_negative_atomic_UI_assignment_cases": atomic_ui_cases,
        "fresh_UI_assignment_cases": fresh_ui_cases,
        "alpha_assignment_cases": alpha_cases,
        "modal_assignment_cases": modal_cases,
        "permutation_assignment_cases": permutation_cases,
        "composite_collision_witness": counterexample_rows,
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
