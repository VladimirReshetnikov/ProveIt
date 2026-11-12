"""Independent, readable checking of the Q-progress rule replacement.

This is a validation tool, not the small checker used for size comparisons.
All substitutions are capture avoiding; bound syntax is compared up to alpha
conversion. It checks the complete eight-rule old/new native calculi.
"""
import copy
import json
from pathlib import Path


def V(x):
    return ["v", x]


Z = ["0"]


def S(t):
    return ["s", t]


def I(n, a, u, h):
    return ["i", n, a, u, h]


def Eq(s, t):
    return ["eq", s, t]


def names(e):
    if isinstance(e, str):
        return {e}
    if isinstance(e, list):
        return set().union(*(names(x) for x in e))
    if isinstance(e, dict):
        return set().union(*(names(x) for x in e.values()))
    return set()


def fresh(used, prefix="fresh"):
    i = 0
    while prefix + str(i) in used:
        i += 1
    name = prefix + str(i)
    used.add(name)
    return name


def fv(e):
    match e:
        case ["v", x]:
            return {x}
        case ["0"]:
            return set()
        case ["s", t]:
            return fv(t)
        case ["i", n, a, u, h]:
            return fv(n) | fv(a) | (fv(h) - {u})
        case ["eq", s, t]:
            return fv(s) | fv(t)
        case ["q", y, b]:
            return fv(b) - {y}
        case ["d", x, y, b]:
            return fv(b) - {x, y}
    raise ValueError("invalid expression")


def under(body, bound, x, t):
    bound = list(bound)
    if x in bound:
        return bound, body
    used = names(body) | names(t) | {x} | set(bound)
    for i, b in enumerate(bound):
        if b in fv(t) and x in fv(body):
            b1 = fresh(used, b + "_")
            body = sub(body, b, V(b1))
            bound[i] = b1
    return bound, sub(body, x, t)


def sub(e, x, t):
    match e:
        case ["v", y]:
            return t if y == x else e
        case ["0"]:
            return e
        case ["s", a]:
            return S(sub(a, x, t))
        case ["i", n, a, u, h]:
            (u1,), h1 = under(h, [u], x, t)
            return I(sub(n, x, t), sub(a, x, t), u1, h1)
        case ["eq", a, b]:
            return Eq(sub(a, x, t), sub(b, x, t))
        case ["q", y, b]:
            (y1,), b1 = under(b, [y], x, t)
            return ["q", y1, b1]
        case ["d", a, b, c]:
            (a1, b1), c1 = under(c, [a, b], x, t)
            return ["d", a1, b1, c1]
    raise ValueError("invalid expression")


def normal(e, env=(), sort="formula"):
    if sort == "term":
        match e:
            case ["v", x] if isinstance(x, str):
                return ("bound", env.index(x)) if x in env else ("free", x)
            case ["0"]:
                return ("0",)
            case ["s", a]:
                return ("s", normal(a, env, "term"))
            case ["i", n, a, u, h] if isinstance(u, str):
                return ("i", normal(n, env, "term"), normal(a, env, "term"),
                        normal(h, (u,) + env, "term"))
    else:
        match e:
            case ["eq", s, t]:
                return ("eq", normal(s, env, "term"), normal(t, env, "term"))
            case ["q", y, b] if isinstance(y, str):
                return ("q", normal(b, (y,) + env))
            case ["d", x, y, b] if isinstance(x, str) and isinstance(y, str) and x != y:
                return ("d", normal(b, (y, x) + env))
    raise ValueError("ill-sorted expression")


def same(a, b):
    return normal(a) == normal(b)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def qinst(q, t):
    require(q[0] == "q", "expected Q")
    normal(t, sort="term")
    return sub(q[2], q[1], t)


def free_context(context):
    return set().union(*(fv(a) for a in context))


def derive(p, context=(), calculus="new"):
    r = p["rule"]
    if r == "hyp":
        a = p["formula"]
        require(any(same(a, b) for b in context), "missing hypothesis")
    elif r == "i0":
        a = Eq(I(Z, p["a"], p["u"], p["h"]), p["a"])
    elif r == "is":
        n, init, u, h = (p[k] for k in ("n", "a", "u", "h"))
        a = Eq(I(S(n), init, u, h), sub(h, u, I(n, init, u, h)))
    elif r == "tr":
        eq = derive(p["major"], context, calculus)
        require(eq[0] == "eq", "transport major is not equality")
        before = derive(p["minor"], context, calculus)
        require(same(before, sub(p["template"], p["hole"], eq[1])), "transport mismatch")
        a = sub(p["template"], p["hole"], eq[2])
    elif r == "qe":
        q = derive(p["major"], context, calculus)
        before = derive(p["base"], context, calculus)
        require(same(before, qinst(q, Z)), "QE base mismatch")
        a = qinst(q, p["term"])
    elif r == "de":
        d = derive(p["major"], context, calculus)
        require(d[0] == "d", "DE major is not D")
        b = p["eigen"]
        require(b not in free_context(context) | fv(d), "DE freshness")
        q = sub(["q", d[2], d[3]], d[1], V(b))
        a = derive(p["body"], (*context, q), calculus)
        require(b not in fv(a), "DE eigenvariable escapes")
    elif r in ("dcase", "dprog"):
        require(r != "dprog" or calculus == "old", "D-progress not primitive here")
        x, y, b, t, z = (p[k] for k in ("x", "y", "matrix", "witness", "eigen"))
        a = ["d", x, y, b]
        normal(a)
        require(r != "dprog" or b[0] == "eq", "compound D-progress")
        require(z not in free_context(context) | fv(a) | fv(t), "D introduction freshness")
        q = sub(["q", y, b], x, t)
        hyp = qinst(q, Z if r == "dcase" else V(z))
        result = derive(p["step"], (*context, hyp), calculus)
        require(same(result, qinst(q, S(V(z)))), "D introduction step mismatch")
    elif r == "qprog":
        require(calculus == "new", "Q-progress not primitive here")
        y, b, z = (p[k] for k in ("y", "matrix", "eigen"))
        a = ["q", y, b]
        require(b[0] == "eq", "compound Q-progress")
        require(z not in free_context(context) | fv(a), "Q-progress freshness")
        result = derive(p["step"], (*context, qinst(a, V(z))), calculus)
        require(same(result, qinst(a, S(V(z)))), "Q-progress step mismatch")
    else:
        raise ValueError("unknown rule")
    normal(a)
    return a


PROOF_KEYS = ("major", "minor", "base", "body", "step")


def translate(p, target, context=()):
    used = names(p) | names(list(context))

    def go(p):
        p = copy.deepcopy(p)
        for k in PROOF_KEYS:
            if k in p:
                p[k] = go(p[k])
        if p["rule"] == "qprog" and target == "old":
            x, b = fresh(used, "unused"), fresh(used, "witness")
            q = ["q", p["y"], p["matrix"]]
            return {"rule": "de", "eigen": b,
                    "major": {"rule": "dprog", "x": x, "y": p["y"],
                              "matrix": p["matrix"], "witness": Z,
                              "eigen": p["eigen"], "step": p["step"]},
                    "body": {"rule": "hyp", "formula": q}}
        if p["rule"] == "dprog" and target == "new":
            z = fresh(used, "case")
            q = sub(["q", p["y"], p["matrix"]], p["x"], p["witness"])
            qp = {"rule": "qprog", "y": q[1], "matrix": q[2],
                  "eigen": p["eigen"], "step": p["step"]}
            return {"rule": "dcase", "x": p["x"], "y": p["y"],
                    "matrix": p["matrix"], "witness": p["witness"], "eigen": z,
                    "step": {"rule": "qe", "major": qp,
                             "base": {"rule": "hyp", "formula": qinst(q, Z)},
                             "term": S(V(z))}}
        return p

    return go(p)


def count(p):
    return 1 + sum(count(p[k]) for k in PROOF_KEYS if k in p)


def successor_iteration_example():
    u, y, z, w, n = "u", "y", "z", "w", "n"
    h = S(V(u))
    f = lambda t: I(t, Z, u, h)
    matrix = Eq(f(V(y)), V(y))
    step = {"rule": "tr", "hole": w,
            "template": Eq(f(S(V(z))), S(V(w))),
            "major": {"rule": "hyp", "formula": Eq(f(V(z)), V(z))},
            "minor": {"rule": "is", "n": V(z), "a": Z, "u": u, "h": h}}
    proof = {"rule": "qe", "term": V(n),
             "major": {"rule": "qprog", "y": y, "matrix": matrix,
                       "eigen": z, "step": step},
             "base": {"rule": "i0", "a": Z, "u": u, "h": h}}
    return proof, Eq(f(V(n)), V(n))


def arbitrary_witness_example():
    # The witness's free y deliberately matches the D index binder. A correct
    # substitution must rename that binder, preserving the witness parameter.
    x, y, u, z, w = "x", "y", "u", "z", "w"
    t = V(y)
    f = lambda n, a: I(n, a, u, V(u))
    matrix = Eq(f(V(y), V(x)), V(x))
    step = {"rule": "tr", "hole": w,
            "template": Eq(f(S(V(z)), t), V(w)),
            "major": {"rule": "hyp", "formula": Eq(f(V(z), t), t)},
            "minor": {"rule": "is", "n": V(z), "a": t, "u": u, "h": V(u)}}
    return {"rule": "dprog", "x": x, "y": y, "matrix": matrix,
            "witness": t, "eigen": z, "step": step}, ["d", x, y, matrix]


def run():
    new, goal = successor_iteration_example()
    old = translate(new, "old")
    new_roundtrip = translate(old, "new")
    result = {"example": "I(n,0;u.Su)=n", "goal": goal, "checks": []}
    for label, proof, calculus in (("new", new, "new"), ("old", old, "old"),
                                   ("new_roundtrip", new_roundtrip, "new")):
        require(same(derive(proof, calculus=calculus), goal), label + " wrong goal")
        result["checks"].append({"name": label, "accepted": True, "nodes": count(proof)})
        Path(label + "_proof.json").write_text(json.dumps({"goal": goal, "proof": proof}, indent=2) + "\n")
    # Verify context preservation, including a context mentioning the default
    # fresh-name prefixes: the translator must choose another unused name.
    context = [Eq(V("witness0"), V("case0")), Eq(V("unused0"), V("unused0"))]
    old_contextual = translate(new, "old", context)
    require(same(derive(old_contextual, context, "old"), goal), "context lost")
    result["contextual_translation"] = True
    witness_old, witness_goal = arbitrary_witness_example()
    witness_new = translate(witness_old, "new")
    for label, proof, calculus in (("witness_old", witness_old, "old"),
                                   ("witness_new", witness_new, "new")):
        require(same(derive(proof, calculus=calculus), witness_goal), label + " wrong goal")
        result["checks"].append({"name": label, "accepted": True, "nodes": count(proof)})
        Path(label + "_proof.json").write_text(json.dumps({"goal": witness_goal, "proof": proof}, indent=2) + "\n")
    result["free_witness_name_preserved_across_binder"] = True
    bad_matrix = ["q", "inner", Eq(Z, Z)]
    bad = {"rule": "qprog", "y": "index", "matrix": bad_matrix,
           "eigen": "step", "step": {"rule": "hyp", "formula": bad_matrix}}
    try:
        derive(bad, calculus="new")
    except ValueError:
        result["compound_progress_rejected"] = True
    else:
        raise AssertionError("accepted compound induction")
    # These are invalid derivations violating eigenvariable side conditions.
    # Use a correctly instantiated step, so a missing freshness guard really
    # would accept it. N(y) alternates 0,1,0,...; with n=1 the retained premise
    # N(S n)=0 is true, while Q_y(N(y)=0) is false since N(0)=0 and N(1)=1.
    parity = lambda t: I(t, Z, "state", I(V("state"), S(Z), "reset", Z))
    matrix = Eq(parity(V("y")), Z)
    captured_premise = Eq(parity(S(V("n"))), Z)
    captured_context = [captured_premise]
    bad = {"rule": "qprog", "y": "y", "matrix": matrix, "eigen": "n",
           "step": {"rule": "hyp", "formula": captured_premise}}
    try:
        derive(bad, captured_context, "new")
    except ValueError:
        result["retained_context_capture_rejected"] = True
    else:
        raise AssertionError("accepted captured eigenvariable")
    # Rule-level guard ablation: perform every Q-progress check except its
    # freshness test. This leaves the production checker untouched and shows
    # that the negative fixture does not fail merely by a step mismatch.
    q = ["q", bad["y"], bad["matrix"]]
    require(bad["matrix"][0] == "eq", "ablation matrix is not an equation")
    require(bad["eigen"] in free_context(captured_context), "fixture is not captured")
    require(bad["eigen"] not in fv(q), "fixture has a second freshness defect")
    ablated_step = derive(bad["step"],
                          (*captured_context, qinst(q, V(bad["eigen"]))), "new")
    require(same(ablated_step, qinst(q, S(V(bad["eigen"])))),
            "ablation has a step mismatch")
    normal(q)
    result["retained_context_capture_guard_ablation_accepts"] = True
    bad = {"rule": "de", "eigen": "n", "major": old["major"]["major"],
           "body": {"rule": "qe", "term": V("n"),
                    "major": {"rule": "hyp", "formula": ["q", new["major"]["y"], new["major"]["matrix"]]},
                    "base": new["base"]}}
    try:
        derive(bad, calculus="old")
    except ValueError:
        result["existential_eigenvariable_escape_rejected"] = True
    else:
        raise AssertionError("accepted escaping eigenvariable")
    # Substitution across a binder must rename it rather than capture y.
    capture = sub(["q", "y", Eq(V("x"), V("y"))], "x", V("y"))
    require(fv(capture) == {"y"}, "capture-avoiding substitution failed")
    result["capture_avoiding_substitution"] = True
    Path("audit_results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    run()
