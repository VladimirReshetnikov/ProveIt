"""Untrusted constructor of explicit proof trees for the new zero theorem.

The generated trees use only rules of checker_constantfree.py. The checker
does not import this file and does not run a numerical evaluator.
"""

from pathlib import Path
import json
import checker_constantfree as C

V = lambda name: ["v", name]
E = C.equality
Z = C.zero
U = C.unit
S = C.successor
O = C.one


def node(rule, conclusion, **fields):
    return {"rule": rule, "conclusion": conclusion, **fields}


def goal(proof):
    return proof["conclusion"]


def refl(t):
    return node("refl", E(t, t))


def replace(equation, proof, motive):
    result = C.substitute(motive, {"replacement": goal(equation)[2]})
    return node("eq_elim", result, equality=equation, premise=proof,
                variable="replacement", motive=motive)


def sym(proof):
    left = goal(proof)[1]
    return replace(proof, refl(left), E(V("replacement"), left))


def trans(first, second):
    return replace(second, first, E(goal(first)[1], V("replacement")))


def jzero(counter_term, anchor):
    assert counter_term[0] == "j" and C.same(counter_term[1], Z(anchor))
    return node("j_zero", E(counter_term, O(anchor)), anchor=anchor)


def compute(previous, output, instruction_proof, anchor, increment=False):
    _, n, i, r, body = previous
    graph = C.step_graph(n, i, r, body, output, anchor)
    axiom = node("j_step", graph, counter=n, index=i, state=r,
                 body=body, output=output, anchor=anchor)
    backward = node("and_right", graph[2], proof=axiom)
    cases = graph[2][1]
    if increment:
        pair = node("and_intro", cases[1], left=instruction_proof,
                    right=refl(output))
        disjunction = node("or_left", cases, proof=pair)
    else:
        disjunction = node("or_right", cases, proof=instruction_proof)
    return node("imp_elim", graph[2][2], implication=backward,
                argument=disjunction)


def K(t):
    return ["j", t, "counter", "register", V("counter")]


def L(t):
    return ["j", t, "counter", "register", V("register")]


def K_one(anchor):
    """J(1;i,r.i)=2, using only J0 and the increment branch."""
    z = Z(anchor)
    base = jzero(K(z), anchor)
    step = compute(K(z), S(K(z)), refl(z), anchor, True)
    return replace(base, step, E(K(O(anchor)), S(V("replacement"))))


def U_one(anchor, target):
    """One literal-equation induction proves U(t)=1 for every target."""
    z = Z(anchor)
    equation = E(U(V("indvar")), O(anchor))
    base = jzero(U(z), anchor)
    current = U(V("indcounter"))
    hypothesis = node("hyp", E(current, O(anchor)), index=0)
    instruction = replace(sym(hypothesis), K_one(anchor),
                          E(K(V("replacement")), S(O(anchor))))
    step = compute(current, O(anchor), instruction, anchor)
    return node("induction", E(U(target), O(anchor)), variable="indvar",
                equation=equation, term=target, eigen="indcounter",
                base=base, step=step, anchor=anchor)


def L_one(anchor):
    """J(1;i,r.r)=0 by one load, because its old register is one."""
    previous = L(Z(anchor))
    return compute(previous, Z(anchor), jzero(previous, anchor), anchor)


def zero_independent(anchor, target):
    unit_proof = U_one(anchor, target)
    result = replace(sym(unit_proof), L_one(anchor),
                     E(L(V("replacement")), Z(anchor)))
    assert C.same(goal(result), E(Z(target), Z(anchor)))
    return result


def all_intro(variable, proof):
    return node("all_intro", ["all", variable, goal(proof)],
                eigen=variable, proof=proof)


def universally_close(proof, variables):
    for variable in reversed(variables):
        proof = all_intro(variable, proof)
    return proof


def package(proof):
    return {"goal": goal(proof), "proof": proof}


def weaken(proof, count):
    """Prefix unused assumptions, shifting every explicit hypothesis index."""
    if isinstance(proof, list):
        return [weaken(value, count) for value in proof]
    if not isinstance(proof, dict):
        return proof
    result = {key: weaken(value, count) for key, value in proof.items()}
    if result.get("rule") == "hyp":
        result["index"] += count
    return result


def main():
    root = Path(__file__).resolve().parents[1]
    destination = root / "certificates"
    destination.mkdir(exist_ok=True)
    a, t = V("a"), V("t")
    proofs = {
        "unit_is_one": universally_close(U_one(a, t), ("a", "t")),
        "anchor_independence": universally_close(zero_independent(a, t), ("a", "t")),
    }
    # The fixed point Z(Z(a))=Z(a) yields Z(a)=Z(Z(a)).
    fixed = sym(zero_independent(a, Z(a)))
    existential = ["ex", "z", E(V("z"), Z(V("z")))]
    exists_proof = node("ex_intro", existential, witness=Z(a), proof=fixed)
    proofs["zero_exists"] = node("parameter", existential, eigen="a", proof=exists_proof)
    # If x and y are fixed points of Z, anchor independence forces x=y.
    x, y = V("x"), V("y")
    fixed_x, fixed_y = E(x, Z(x)), E(y, Z(y))
    both = ["and", fixed_x, fixed_y]
    hypothesis = node("hyp", both, index=0)
    px = node("and_left", fixed_x, proof=hypothesis)
    py = node("and_right", fixed_y, proof=hypothesis)
    # Re-use a closed theorem via quantifier elimination to avoid changing
    # its internal structure; weaken prefixes the unused outer assumption.
    universal = weaken(proofs["anchor_independence"], 1)
    ax = node("all_elim", C.substitute(goal(universal)[2], {"a": y}),
              universal=universal, term=y)
    ay = node("all_elim", E(Z(x), Z(y)), universal=ax, term=x)
    equality = trans(trans(px, ay), sym(py))
    unique = node("imp_intro", ["imp", both, E(x, y)], proof=equality)
    proofs["zero_unique"] = universally_close(unique, ("x", "y"))
    for name, proof in proofs.items():
        certificate = package(proof)
        C.check_certificate(certificate)
        path = destination / (name + ".json")
        path.write_text(json.dumps(certificate, separators=(",", ":")) + "\n")
        print(name, path.stat().st_size)


if __name__ == "__main__":
    main()
