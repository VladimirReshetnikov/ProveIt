"""Untrusted constructors for symbolic RL/CC proof certificates.

No producer function is imported by checker.py. The constructions below
expand into primitive proof trees before they are submitted for checking.
"""
import copy
import json
from pathlib import Path


def Z():
    return ["0"]


def V(name):
    return ["v", name]


def S(t):
    return ["S", t]


def R(n, a, u, v, h):
    return ["R", n, a, u, v, h]


def E(s, t):
    return ["=", s, t]


def Q(y, body):
    return ["Q", y, body]


def D(x, y, body):
    return ["D", x, y, body]


def replace(tree, mapping):
    """Named substitution for these deliberately fresh producer templates."""
    tag = tree[0]
    if tag == "v":
        return copy.deepcopy(mapping.get(tree[1], tree))
    if tag == "0":
        return tree
    if tag == "R":
        _, n, a, u, v, h = tree
        inner = {k: value for k, value in mapping.items() if k not in (u, v)}
        return R(replace(n, mapping), replace(a, mapping), u, v, replace(h, inner))
    if tag in ("D", "Q"):
        binders = tree[1:-1]
        inner = {k: value for k, value in mapping.items() if k not in binders}
        return tree[:-1] + [replace(tree[-1], inner)]
    return [tag] + [replace(child, mapping) for child in tree[1:]]


def rzero(a, h=Z(), u="ru", v="rv"):
    return (R(Z(), a, u, v, h), S(a), {"rule": "R0"})


def rstep(n, a, h, u="ru", v="rv"):
    recursive = R(n, a, u, v, h)
    result = replace(h, {u: n, v: recursive})
    return (R(S(n), a, u, v, h), result, {"rule": "RS"})


def rl(major, minor):
    source, target, p = major
    same, result, q = minor
    assert source == same
    return (target, result, {"rule": "RL", "equality": E(source, target),
                            "major": p, "minor": q})


def reflexivity(t):
    computation = rstep(t, Z(), V("ref_u"), "ref_u", "ref_v")
    return rl(computation, computation)


def symmetry(proof):
    return rl(proof, reflexivity(proof[0]))


def transitivity(left, right):
    assert left[1] == right[0]
    return rl(symmetry(left), right)


def cc(proof, a, h, u="ccu", v="ccv"):
    s, t, p = proof
    return (R(s, a, u, v, h), R(t, a, u, v, h),
            {"rule": "CC", "major": p})


def W(t):
    return R(t, Z(), "wu", "wv", V("wu"))


def H(F, t):
    return R(t, F(Z()), "hu", "hv", S(F(S(V("hu")))))


def J(F, t):
    return W(H(F, t))


def bridge_base(F):
    first = rzero(F(Z()), S(F(S(V("hu")))), "hu", "hv")
    lifted = cc(first, Z(), V("wu"), "wu", "wv")
    last = rstep(F(Z()), Z(), V("wu"), "wu", "wv")
    return transitivity(lifted, last)


def bridge_step(F, n):
    first = rstep(n, F(Z()), S(F(S(V("hu")))), "hu", "hv")
    lifted = cc(first, Z(), V("wu"), "wu", "wv")
    last = rstep(F(S(n)), Z(), V("wu"), "wu", "wv")
    return transitivity(lifted, last)


def bridge(F, t, context_size=0, suffix="0"):
    """Prove J_F(t)=F(t) by numerical cases, with symbolic t."""
    x, y = "bx" + suffix, "by" + suffix
    z, a = "bz" + suffix, "ba" + suffix
    matrix = E(J(F, V(y)), F(V(y)))
    paired = D(x, y, matrix)
    intro = {"rule": "DI", "mode": "case", "witness": Z(), "eigen": z,
             "body": bridge_step(F, V(z))[2]}
    use = {"rule": "QE", "closure": Q(y, matrix), "target": t,
           "major": {"rule": "hyp", "index": context_size},
           "base": bridge_base(F)[2]}
    proof = {"rule": "DE", "paired": paired, "major": intro,
             "eigen": a, "body": use}
    return J(F, t), F(t), proof


def congruence(F, equality, context_size=0, suffix="0"):
    """Expand arbitrary fixed unary-template congruence using only RL/CC."""
    s, t, p = equality
    inner = cc(equality, F(Z()), S(F(S(V("hu")))), "hu", "hv")
    outer = cc(inner, Z(), V("wu"), "wu", "wv")
    left = symmetry(bridge(F, s, context_size, "s" + suffix))
    right = bridge(F, t, context_size, "t" + suffix)
    return transitivity(left, transitivity(outer, right))


def packet(proof, parameters=()):
    left, right, derivation = proof
    return {"parameters": list(parameters), "goal": E(left, right), "proof": derivation}


def induction_packet(retain_closure=False):
    """R(n,0;u,v.Sv)=Sn, with a real equation-induction step."""
    u, v = "iu", "iv"
    update = S(V(v))
    iterator = lambda n: R(n, Z(), u, v, update)
    equation = lambda n: E(iterator(n), S(n))
    prefix = 1 if retain_closure else 0
    z = "ind_z"
    induction_hypothesis = (iterator(V(z)), S(V(z)),
                            {"rule": "hyp", "index": prefix})
    lifted = congruence(S, induction_hypothesis, prefix + 1, "ind")
    computation = rstep(V(z), Z(), update, u, v)
    step = transitivity(computation, lifted)
    paired = D("ind_x", "ind_y", equation(V("ind_y")))
    intro = {"rule": "DI", "mode": "progress", "witness": Z(),
             "eigen": z, "body": step[2]}
    main = {"rule": "DE", "paired": paired, "major": intro,
            "eigen": "ind_a", "body": {
                "rule": "QE", "closure": Q("ind_y", equation(V("ind_y"))),
                "target": V("n"), "major": {"rule": "hyp", "index": prefix},
                "base": rzero(Z(), update, u, v)[2]}}
    if retain_closure:
        neutral = D("keep_x", "keep_y", E(V("keep_y"), V("keep_y")))
        neutral_intro = {"rule": "DI", "mode": "case", "witness": Z(),
                         "eigen": "keep_z", "body": reflexivity(S(V("keep_z")))[2]}
        main = {"rule": "DE", "paired": neutral, "major": neutral_intro,
                "eigen": "keep_a", "body": main}
    return {"parameters": ["n"], "goal": equation(V("n")), "proof": main}


def cases():
    positive = {}
    positive["R0_symbolic_seed"] = packet(rzero(V("a")), ["a"])
    positive["RS_counter"] = packet(rstep(V("n"), V("a"), V("u"), "u", "v"), ["n", "a"])
    positive["RS_state"] = packet(rstep(V("n"), V("a"), V("v"), "u", "v"), ["n", "a"])
    nested = R(V("v"), V("a"), "inner_u", "inner_v", S(V("u")))
    positive["RS_nested_binding"] = packet(rstep(V("n"), V("a"), nested, "u", "v"), ["n", "a"])
    positive["reflexivity_symbolic"] = packet(reflexivity(V("a")), ["a"])
    source = rstep(V("a"), Z(), V("su"), "su", "sv")
    positive["direct_counter_congruence"] = packet(cc(source, V("b"), S(V("cv")), "cu", "cv"), ["a", "b"])
    positive["derived_successor_congruence"] = packet(congruence(S, source), ["a"])
    F = lambda x: R(V("q"), x, "fu", "fv", S(V("fv")))
    positive["derived_seed_congruence_with_parameter"] = packet(congruence(F, source), ["a", "q"])
    G = lambda x: R(V("q"), V("b"), "fu", "fv", R(x, V("fv"), "gu", "gv", S(V("gu"))))
    positive["derived_update_congruence_with_parameters"] = packet(congruence(G, source), ["a", "q", "b"])
    positive["equation_induction"] = induction_packet()
    positive["contextual_equation_induction"] = induction_packet(True)
    alpha = copy.deepcopy(positive["direct_counter_congruence"])
    alpha["goal"][2][3:5] = ["other_u", "other_v"]
    alpha["goal"][2][5] = S(V("other_v"))
    positive["alpha_equivalent_updates"] = alpha

    negative = {}
    bad = copy.deepcopy(positive["R0_symbolic_seed"])
    bad["goal"][2] = Z()
    negative["wrong_R0_result"] = bad
    bad = copy.deepcopy(positive["RS_counter"])
    bad["goal"][2] = R(V("n"), V("a"), "u", "v", V("u"))
    negative["counter_state_confusion"] = bad
    bad = copy.deepcopy(positive["direct_counter_congruence"])
    bad["goal"][2][2] = Z()
    negative["primitive_CC_changes_seed"] = bad
    bad = copy.deepcopy(positive["direct_counter_congruence"])
    bad["goal"][2][5] = Z()
    negative["primitive_CC_changes_update"] = bad
    negative["primitive_CC_at_successor"] = {
        "parameters": ["a"], "goal": E(S(source[0]), S(source[1])),
        "proof": {"rule": "CC", "major": source[2]}}
    negative["false_equation"] = {"goal": E(Z(), S(Z())), "proof": {"rule": "hyp", "index": 0}}
    negative["compound_progress"] = {
        "goal": D("x", "y", D("u", "v", E(Z(), Z()))),
        "proof": {"rule": "DI", "mode": "progress", "witness": Z(),
                  "eigen": "z", "body": {"rule": "hyp", "index": 0}}}
    bad = copy.deepcopy(positive["equation_induction"])
    bad["proof"]["major"]["witness"] = V("ind_z")
    negative["witness_uses_future_eigenparameter"] = bad
    bad = copy.deepcopy(positive["equation_induction"])
    bad["proof"]["eigen"] = "n"
    negative["DE_eigenparameter_not_fresh"] = bad
    bad = copy.deepcopy(positive["R0_symbolic_seed"])
    bad["parameters"] = []
    negative["unbound_numerical_parameter"] = bad
    negative["Q_exported_as_object"] = {
        "goal": Q("y", E(V("y"), V("y"))),
        "proof": {"rule": "hyp", "index": 0}}
    bad = copy.deepcopy(positive["equation_induction"])
    bad["proof"]["body"]["major"] = {"rule": "DE"}
    negative["non_hypothesis_Q_major"] = bad
    return positive, negative


def main():
    root = Path(__file__).resolve().parent
    output = root / "certificates"
    output.mkdir(exist_ok=True)
    positives, negatives = cases()
    rows = []
    for expected, group in ((True, positives), (False, negatives)):
        for name, data in group.items():
            path = output / (name + ".json")
            path.write_text(json.dumps(data, indent=2) + "\n")
            rows.append({"name": name, "expected": expected, "file": str(path.relative_to(root))})
    (root / "cases.json").write_text(json.dumps(rows, indent=2) + "\n")
    print(json.dumps({"positive": len(positives), "negative": len(negatives)}))


if __name__ == "__main__":
    main()
