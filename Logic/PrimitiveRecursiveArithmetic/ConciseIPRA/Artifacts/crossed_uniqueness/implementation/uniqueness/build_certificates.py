#!/usr/bin/env python3
"""Expand derived equational rules into the six primitive proof forms.

The generator is untrusted. Every output is rechecked by uniqueness_checker.
There is no numerical-case rule in that checker: cases below expand to
di/de/qe/hyp, with explicit variable and context weakening of subproofs.
"""

import json
from pathlib import Path
from uniqueness_checker import (Z, S, I, Eq, Q, D, lift_t, lift_f, sub_t,
                                sub_f, nf_f, infer, check)


OUT = Path(__file__).with_name("certificates")


def C(n, a, b):
    return I(n, a, lift_t(b))


def lift_proof(p, amount=1, cutoff=0):
    tag = p[0]
    if tag == "hyp":
        return list(p)
    if tag == "refl":
        return [tag, lift_t(p[1], amount, cutoff)]
    if tag == "qe":
        return [tag, lift_proof(p[1], amount, cutoff),
                lift_proof(p[2], amount, cutoff),
                lift_t(p[3], amount, cutoff)]
    if tag == "de":
        return [tag, lift_proof(p[1], amount, cutoff),
                lift_proof(p[2], amount, cutoff + 1)]
    if tag == "di":
        return [tag, lift_f(p[1], amount, cutoff + 2),
                lift_t(p[2], amount, cutoff),
                lift_proof(p[3], amount, cutoff + 1)]
    if tag == "u":
        return [tag, lift_t(p[1], amount, cutoff + 1),
                lift_t(p[2], amount, cutoff),
                lift_t(p[3], amount, cutoff + 1),
                lift_t(p[4], amount, cutoff),
                lift_proof(p[5], amount, cutoff),
                lift_proof(p[6], amount, cutoff + 1)]
    raise ValueError(tag)


def add_assumption(p, at):
    """Insert an unused assumption at the chosen outer context position."""
    tag = p[0]
    if tag == "hyp":
        return [tag, p[1] + int(p[1] >= at)]
    if tag == "refl":
        return list(p)
    q = list(p)
    proof_positions = {"qe": (1, 2), "de": (1, 2), "di": (3,),
                       "u": (5, 6)}[tag]
    for pos in proof_positions:
        q[pos] = add_assumption(p[pos], at)
    return q


def symmetry(s, t, proof):
    """s=t gives t=s: U on a constant function, at counter zero."""
    f = lift_t(s)
    return ["u", f, t, 0, Z, proof, ["refl", lift_t(s)]]


def crossed_congruence(s, t, body, proof):
    """s=t gives body(t)=body(s), using a one-step iterator."""
    f = I(0, lift_t(s), lift_t(body, cutoff=1))
    f1 = lift_t(f, cutoff=1)
    step_value = sub_t(f1, (S(0),))
    return ["u", f, t, body, S(Z), proof, ["refl", step_value]]


def cases(body, target, base_proof, successor_proof, context_length):
    """E(0), E(Sz) |- E(target), expanded with DI/DE/QE.

    body has its case variable at index 0. successor_proof is over the
    numerically lifted outer context, with one fresh predecessor variable.
    """
    matrix = lift_f(body, cutoff=1)  # insert unused D witness at index 1
    introduction = ["di", matrix, Z,
                    add_assumption(successor_proof, context_length)]
    opened_base = add_assumption(lift_proof(base_proof), context_length)
    branch = ["qe", ["hyp", context_length], opened_base, lift_t(target)]
    return ["de", introduction, branch]


def join(s, t, u, st_proof, su_proof, context_length):
    """s=t and s=u give t=u, with a genuinely used numerical case proof."""
    f = C(0, lift_t(s), lift_t(u))
    s1, u1 = lift_t(s), lift_t(u)
    su1 = lift_proof(su_proof)
    # At the U recurrence eigenvariable z, prove u=C(z,s,u) by cases.
    case_body = Eq(lift_t(u1), C(0, lift_t(s1), lift_t(u1)))
    zero = symmetry(s1, u1, su1)
    successor = ["refl", lift_t(u1)]
    recurrence = cases(case_body, 0, zero, successor, context_length)
    return ["u", f, t, 0, S(Z), st_proof, recurrence]


def save(name, scope, context, goal, proof):
    record = {"scope": scope, "context": list(context),
              "goal": goal, "proof": proof}
    check(record)
    path = OUT / (name + ".json")
    path.write_text(json.dumps(record, indent=2) + "\n")
    return {"name": name, "bytes": path.stat().st_size,
            "scope": scope, "assumptions": len(context),
            "status": "ACCEPT"}


def generate():
    OUT.mkdir(exist_ok=True)
    result = []
    result.append(save("closed_reflexivity", 0, (), Eq(Z, Z), ["refl", Z]))
    result.append(save("symmetry", 2, (Eq(0, 1),), Eq(1, 0),
                       symmetry(0, 1, ["hyp", 0])))
    # An arbitrary context h(v)=I(v,s;u.Su), with s as a passive parameter.
    body = I(0, 1, S(0))
    result.append(save("crossed_congruence", 2, (Eq(0, 1),),
                       Eq(sub_t(body, (1,)), sub_t(body, (0,))),
                       crossed_congruence(0, 1, body, ["hyp", 0])))
    joined = join(0, 1, 2, ["hyp", 0], ["hyp", 1], 2)
    result.append(save("common_source_join", 3, (Eq(0, 1), Eq(0, 2)),
                       Eq(1, 2), joined))
    # Transitivity is a common-source join after reversing its first input.
    trans = join(1, 0, 2, symmetry(0, 1, ["hyp", 0]), ["hyp", 1], 2)
    result.append(save("transitivity", 3, (Eq(0, 1), Eq(1, 2)),
                       Eq(0, 2), trans))
    # Non-definitional iteration laws, at a free counter.
    result.append(save("identity_iteration", 1, (), Eq(I(0, Z, 0), Z),
                       ["u", Z, Z, 0, 0, ["refl", Z], ["refl", Z]]))
    result.append(save("successor_iteration", 1, (), Eq(I(0, Z, S(0)), 0),
                       ["u", 0, Z, S(0), 0,
                        ["refl", Z], ["refl", S(0)]]))
    # A closed theorem with D, showing use of introduction and elimination
    # certificates is possible from an empty parameter scope.
    matrix = Eq(Z, Z)
    result.append(save("closed_D_truth", 0, (), D(matrix),
                       ["di", matrix, Z, ["refl", Z]]))
    return result


if __name__ == "__main__":
    print(json.dumps(generate(), indent=2))
