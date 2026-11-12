"""Small, explicit equational certificate checker for the three-schema BJ basis.

This is a supporting equational checker, not a complete iPRA proof checker.
Terms are zero 0, ["v", name], ["B", left, right], ["h", argument], and
["J", counter, binder, body].  The fixed unary symbol h is uninterpreted.
Only the J body binds its variable.  No arithmetic evaluator is trusted.
"""
import json
import re
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def name(value):
    require(isinstance(value, str) and re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", value),
            "invalid variable or lemma name")
    return value


def term(t):
    if type(t) is int and t == 0:
        return
    require(type(t) is list and len(t) > 0, "invalid term")
    tag = t[0]
    if tag == "v":
        require(len(t) == 2, "variable arity")
        name(t[1])
    elif tag == "B":
        require(len(t) == 3, "B arity")
        term(t[1]); term(t[2])
    elif tag == "h":
        require(len(t) == 2, "h arity")
        term(t[1])
    elif tag == "J":
        require(len(t) == 4, "J arity")
        term(t[1]); name(t[2]); term(t[3])
    else:
        raise ValueError("unknown term constructor")


def free(t):
    if t == 0:
        return set()
    if t[0] == "v":
        return {t[1]}
    if t[0] == "B":
        return free(t[1]) | free(t[2])
    if t[0] == "h":
        return free(t[1])
    return free(t[1]) | (free(t[3]) - {t[2]})


def names(t):
    if t == 0:
        return set()
    if t[0] == "v":
        return {t[1]}
    if t[0] == "B":
        return names(t[1]) | names(t[2])
    if t[0] == "h":
        return names(t[1])
    return names(t[1]) | names(t[3]) | {t[2]}


def subst(t, images):
    """Simultaneous capture-avoiding substitution, with explicit fresh renaming."""
    if t == 0:
        return 0
    if t[0] == "v":
        return images.get(t[1], t)
    if t[0] == "B":
        return ["B", subst(t[1], images), subst(t[2], images)]
    if t[0] == "h":
        return ["h", subst(t[1], images)]
    counter, binder, body = t[1:]
    active = {k: v for k, v in images.items() if k != binder}
    image_free = set().union(*(free(v) for v in active.values()))
    if binder in image_free:
        used = names(t) | set(active) | set().union(*(names(v) for v in active.values()))
        fresh = "fresh"
        while fresh in used:
            fresh += "_"
        body = subst(body, {binder: ["v", fresh]})
        binder = fresh
    return ["J", subst(counter, images), binder, subst(body, active)]


def canonical(t, bound=()):
    """A de Bruijn comparison key.  This performs no numerical reduction."""
    if t == 0:
        return ("zero",)
    if t[0] == "v":
        return ("bound", bound.index(t[1])) if t[1] in bound else ("free", t[1])
    if t[0] == "B":
        return ("B", canonical(t[1], bound), canonical(t[2], bound))
    if t[0] == "h":
        return ("h", canonical(t[1], bound))
    return ("J", canonical(t[1], bound), canonical(t[3], (t[2],) + bound))


def same_equation(a, b):
    return all(canonical(x) == canonical(y) for x, y in zip(a, b))


def fields(p, *keys):
    require(type(p) is dict and set(p) == {"r", *keys}, "invalid proof fields")


def successor(t):
    return ["B", 0, t]


def derive(p, lemmas, assumptions=()):
    require(type(p) is dict and type(p.get("r")) is str, "invalid proof node")
    rule = p["r"]
    if rule == "refl":
        fields(p, "term"); term(p["term"])
        return p["term"], p["term"]
    if rule == "hyp":
        fields(p, "index")
        i = p["index"]
        require(type(i) is int and 0 <= i < len(assumptions), "unavailable hypothesis")
        return assumptions[i]
    if rule == "ref":
        fields(p, "name", "sub")
        require(p["name"] in lemmas, "unknown or forward lemma reference")
        require(type(p["sub"]) is dict, "invalid substitution")
        for variable, image in p["sub"].items():
            name(variable); term(image)
        return tuple(subst(t, p["sub"]) for t in lemmas[p["name"]])
    if rule == "B":
        fields(p, "a", "b"); term(p["a"]); term(p["b"])
        return ["B", successor(p["a"]), p["b"]], p["a"]
    if rule in ("J0", "JS"):
        fields(p, "binder", "body", *(["n"] if rule == "JS" else []))
        name(p["binder"]); term(p["body"])
        if rule == "J0":
            return ["J", 0, p["binder"], p["body"]], 0
        term(p["n"])
        old = ["J", p["n"], p["binder"], p["body"]]
        return ["J", successor(p["n"]), p["binder"], p["body"]], subst(p["body"], {p["binder"]: old})
    if rule == "sym":
        fields(p, "proof")
        a, b = derive(p["proof"], lemmas, assumptions)
        return b, a
    if rule == "trans":
        fields(p, "left", "right")
        a, b = derive(p["left"], lemmas, assumptions)
        c, d = derive(p["right"], lemmas, assumptions)
        require(canonical(b) == canonical(c), "transitivity middle mismatch")
        return a, d
    if rule == "cong":
        fields(p, "var", "context", "proof")
        name(p["var"]); term(p["context"])
        a, b = derive(p["proof"], lemmas, assumptions)
        return subst(p["context"], {p["var"]: a}), subst(p["context"], {p["var"]: b})
    if rule == "ind":
        fields(p, "var", "eigen", "lhs", "rhs", "target", "base", "step")
        variable, eigen = name(p["var"]), name(p["eigen"])
        lhs, rhs, target = p["lhs"], p["rhs"], p["target"]
        term(lhs); term(rhs); term(target)
        forbidden = free(lhs) | free(rhs) | free(target)
        for eq in assumptions:
            forbidden |= free(eq[0]) | free(eq[1])
        require(eigen != variable and eigen not in forbidden, "induction eigenvariable is not fresh")
        expected_base = tuple(subst(t, {variable: 0}) for t in (lhs, rhs))
        require(same_equation(derive(p["base"], lemmas, assumptions), expected_base), "induction base mismatch")
        z = ["v", eigen]
        hypothesis = tuple(subst(t, {variable: z}) for t in (lhs, rhs))
        expected_step = tuple(subst(t, {variable: successor(z)}) for t in (lhs, rhs))
        actual_step = derive(p["step"], lemmas, assumptions + (hypothesis,))
        require(same_equation(actual_step, expected_step), "induction step mismatch")
        return tuple(subst(t, {variable: target}) for t in (lhs, rhs))
    raise ValueError("unknown proof rule")


def check(packet):
    require(type(packet) is dict and set(packet) == {"format", "lemmas"}, "invalid packet")
    require(packet["format"] == "BJ-equations-v1" and type(packet["lemmas"]) is list, "invalid format")
    require(bool(packet["lemmas"]), "empty theorem packet")
    lemmas = {}
    for item in packet["lemmas"]:
        require(type(item) is dict and set(item) == {"name", "equation", "proof"}, "invalid lemma")
        label = name(item["name"])
        require(label not in lemmas, "duplicate lemma name")
        equation = item["equation"]
        require(type(equation) is list and len(equation) == 2, "invalid equation")
        term(equation[0]); term(equation[1])
        actual = derive(item["proof"], lemmas)
        require(same_equation(actual, equation), "declared theorem mismatch: " + label)
        lemmas[label] = tuple(equation)
    return lemmas


if __name__ == "__main__":
    try:
        check(json.load(sys.stdin))
    except (ValueError, TypeError, KeyError, IndexError, RecursionError) as error:
        print("REJECT")
        print(str(error), file=sys.stderr)
        sys.exit(1)
    print("ACCEPT")
