#!/usr/bin/env python3
"""Untrusted producer of the explicit symbolic proof and negative controls."""

import copy
import json
from pathlib import Path

from verify_certificate import AXIOMS, ONE, ZERO, f, s, subst_equation, v, w


ROOT = Path(__file__).resolve().parent
proof = []


def node(rule, eq, gamma=(), **fields):
    proof.append({"rule": rule, "context": gamma, "equation": eq, **fields})
    return len(proof) - 1


def ax(name, mapping, gamma=()):
    return node("axiom", subst_equation(AXIOMS[name], mapping), gamma,
                name=name, substitution=mapping)


def refl(t, gamma=()):
    return node("reflexivity", (t, t), gamma)


def sym(p):
    a = proof[p]
    return node("symmetry", tuple(reversed(a["equation"])), a["context"], premise=p)


def congr(symbol, *parents):
    gamma = proof[parents[0]]["context"] if parents else ()
    left = (symbol,) + tuple(proof[p]["equation"][0] for p in parents)
    right = (symbol,) + tuple(proof[p]["equation"][1] for p in parents)
    return node("congruence", (left, right), gamma, symbol=symbol, premises=parents)


def chain(*parents):
    result = parents[0]
    for parent in parents[1:]:
        result = node("transitivity",
                      (proof[result]["equation"][0], proof[parent]["equation"][1]),
                      proof[result]["context"], first=result, second=parent)
    return result


def induction(template, variable, eigen, target, base, step):
    return node("induction", subst_equation(template, {variable: target}),
                template=template, variable=variable, eigenvariable=eigen,
                target=target, base=base, step=step)


n, t, j, r = map(v, ("n", "t", "j", "r"))

# First induction, base:
# W(1,SSn) = F(SSn,W(0,SSn)) = F(SSn,0) = 1 = S W(0,Sn).
b1 = ax("WS", {"t": ZERO, "n": s(s(n))})
b2 = congr("F", refl(s(s(n))), ax("W0", {"n": s(s(n))}))
b3 = ax("FSS0", {"n": n})
b4 = sym(congr("S", ax("W0", {"n": s(n)})))
first_base = chain(b1, b2, b3, b4)

# First induction, step, with exactly the literal-equation hypothesis.
first_ih = (w(s(j), s(s(n))), s(w(j, s(n))))
g1 = (first_ih,)
st1 = ax("WS", {"t": s(j), "n": s(s(n))}, g1)
ih1 = node("hypothesis", first_ih, g1)
st2 = congr("F", refl(s(s(n)), g1), ih1)
st3 = ax("FS", {"n": s(n), "u": w(j, s(n))}, g1)
st4 = sym(congr("S", ax("WS", {"t": j, "n": s(n)}, g1)))
first_step = chain(st1, st2, st3, st4)
orbit_template = (w(s(t), s(s(n))), s(w(t, s(n))))
orbit = induction(orbit_template, "t", "j", t, first_base, first_step)

# Second induction, base: W(1,1) = F(1,W(0,1)) = F(1,0) = 0.
p1 = ax("WS", {"t": ZERO, "n": ONE})
p2 = congr("F", refl(ONE), ax("W0", {"n": ONE}))
p3 = ax("F10", {})
second_base = chain(p1, p2, p3)

# The COMPLETED first theorem may now be specialized t:=Sr and n:=r.
specialization = {"t": s(r), "n": r}
specialized = node("substitution", subst_equation(orbit_template, specialization),
                   premise=orbit, substitution=specialization)
second_ih = (w(s(r), s(r)), r)
g2 = (second_ih,)
specialized_in_context = node("weakening", proof[specialized]["equation"], g2,
                              premise=specialized)
ih2 = node("hypothesis", second_ih, g2)
second_step = chain(specialized_in_context, congr("S", ih2))
predecessor_template = (w(s(n), s(n)), n)
predecessor = induction(predecessor_template, "n", "r", n,
                        second_base, second_step)
zero = ax("W0", {"n": ZERO})

certificate = {
    "format": "diagonal-equation-v1",
    "proof": proof,
    "results": {"orbit_conjugacy": orbit, "predecessor_successor": predecessor,
                "predecessor_zero": zero},
}


def write(name, value):
    (ROOT / name).write_text(json.dumps(value, indent=2) + "\n")


write("certificate.json", certificate)
negative = {}

changed = copy.deepcopy(certificate)
changed["proof"][predecessor]["equation"] = (w(s(n), s(n)), ZERO)
write("negative_changed_endpoint.json", changed)
negative["negative_changed_endpoint.json"] = "induction conclusion does not match"

changed = copy.deepcopy(certificate)
changed["proof"][predecessor]["step"] = ih2
write("negative_invalid_step.json", changed)
negative["negative_invalid_step.json"] = "induction step or its hypothesis does not match"

changed = copy.deepcopy(certificate)
changed["proof"][orbit]["eigenvariable"] = "n"
write("negative_eigenvariable_capture.json", changed)
negative["negative_eigenvariable_capture.json"] = "induction eigenvariable is not fresh"

# A different explicit boundary: substitution must change assumptions too.
x, y = v("x"), v("y")
bad_context = ((x, y),)
changed = {
    "format": "diagonal-equation-v1",
    "proof": [
        {"rule": "hypothesis", "context": bad_context, "equation": (x, y)},
        {"rule": "substitution", "context": bad_context, "equation": (s(x), y),
         "premise": 0, "substitution": {"x": s(x)}},
    ],
    "results": {"false_context_substitution": 1},
}
write("negative_context_substitution.json", changed)
negative["negative_context_substitution.json"] = "substitution did not transform its entire context"
write("negative_controls.json", negative)
print(f"Wrote {len(proof)} proof nodes, exactly two induction nodes, and {len(negative)} negative controls.")
