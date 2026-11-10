"""Complete closed-iteration / raw-reset theory checker.

Replace @@COMPARATOR@@ by the fixed, expanded numerical comparator tree.
The only runtime import is the standard-library JSON parser. Read CHECKER.md
for the finite syntax, proof instructions, and theorem-only public interface.
"""
import json


E = ['I', ['I', ['0'], ['v', 'u'], ['S', ['0']]], ['I', ['0'], ['I', ['I', ['0'], ['v', 'u'], ['S', ['0']]], ['I', ['I', ['S', ['v', 'u']], ['I', ['0'], ['I', ['0'], ['I', ['I', ['0'], ['v', 'u'], ['S', ['0']]], ['v', 'u'], ['0']], ['S', ['0']]], ['v', 'u']], ['I', ['0'], ['I', ['I', ['0'], ['v', 'u'], ['S', ['0']]], ['v', 'u'], ['0']], ['I', ['S', ['I', ['S', ['v', 'u']], ['I', ['I', ['S', ['v', 'u']], ['I', ['S', ['v', 'u']], ['I', ['I', ['0'], ['v', 'u'], ['S', ['0']]], ['v', 'u'], ['0']], ['I', ['I', ['0'], ['v', 'u'], ['S', ['0']]], ['v', 'u'], ['0']]], ['I', ['0'], ['v', 'u'], ['S', ['0']]]], ['v', 'u'], ['0']], ['v', 'u']]], ['v', 'u'], ['0']]]], ['v', 'b'], ['I', ['I', ['S', ['v', 'u']], ['v', 'u'], ['v', 'u']], ['v', 'a'], ['S', ['0']]]], ['0']], ['S', ['0']]], ['I', ['0'], ['I', ['I', ['0'], ['v', 'u'], ['S', ['0']]], ['I', ['I', ['S', ['v', 'u']], ['I', ['0'], ['I', ['0'], ['I', ['I', ['0'], ['v', 'u'], ['S', ['0']]], ['v', 'u'], ['0']], ['S', ['0']]], ['v', 'u']], ['I', ['0'], ['I', ['I', ['0'], ['v', 'u'], ['S', ['0']]], ['v', 'u'], ['0']], ['I', ['S', ['I', ['S', ['v', 'u']], ['I', ['I', ['S', ['v', 'u']], ['I', ['S', ['v', 'u']], ['I', ['I', ['0'], ['v', 'u'], ['S', ['0']]], ['v', 'u'], ['0']], ['I', ['I', ['0'], ['v', 'u'], ['S', ['0']]], ['v', 'u'], ['0']]], ['I', ['0'], ['v', 'u'], ['S', ['0']]]], ['v', 'u'], ['0']], ['v', 'u']]], ['v', 'u'], ['0']]]], ['v', 'a'], ['I', ['I', ['S', ['v', 'u']], ['v', 'u'], ['v', 'u']], ['v', 'b'], ['S', ['0']]]], ['0']], ['S', ['0']]]]
ZERO = ["0"]
ONE = ["S", ZERO]


def require(condition):
    if not condition:
        raise ValueError("invalid certificate")


def name(x):
    require(type(x) is str and bool(x))
    return x


def term(t):
    """Validate a term and return its free numerical names."""
    require(type(t) is list and bool(t))
    if t[0] == "0" and len(t) == 1:
        return set()
    if t[0] == "v" and len(t) == 2:
        return {name(t[1])}
    if t[0] == "S" and len(t) == 2:
        return term(t[1])
    if t[0] == "I" and len(t) == 4:
        require(term(t[1]) <= {"u"})
        return term(t[2]) | term(t[3])
    raise ValueError("invalid numerical term")


def formula(a):
    """Validate a formula and return its free numerical names."""
    require(type(a) is list and bool(a))
    if a[0] == "false" and len(a) == 1:
        return set()
    if a[0] == "eq" and len(a) == 3:
        return term(a[1]) | term(a[2])
    if a[0] in ("and", "or", "imp") and len(a) == 3:
        return formula(a[1]) | formula(a[2])
    if a[0] in ("all", "ex") and len(a) == 3:
        return formula(a[2]) - {name(a[1])}
    raise ValueError("invalid formula")


def replace(t, images):
    """Simultaneous substitution, not descending into closed updates."""
    if t[0] == "v":
        return images.get(t[1], t)
    if t[0] == "S":
        return ["S", replace(t[1], images)]
    if t[0] == "I":
        return ["I", t[1], replace(t[2], images), replace(t[3], images)]
    return t


def names(a):
    """All strings suffice as a conservative set of forbidden fresh names."""
    if type(a) is str:
        return {a}
    if type(a) is list:
        return set().union(*(names(b) for b in a))
    return set()


def subst(a, x, t):
    """Capture-avoiding numerical substitution in a validated formula."""
    tag = a[0]
    if tag == "eq":
        return [tag, replace(a[1], {x: t}), replace(a[2], {x: t})]
    if tag in ("and", "or", "imp"):
        return [tag, subst(a[1], x, t), subst(a[2], x, t)]
    if tag in ("all", "ex"):
        y, body = a[1:]
        if y == x or x not in formula(body):
            return a
        if y in term(t):
            used = names(body) | names(t) | {x, y}
            fresh = "_"
            while fresh in used:
                fresh += "_"
            body = subst(body, y, ["v", fresh])
            y = fresh
        return [tag, y, subst(body, x, t)]
    return a


def canonical_term(t, bound):
    if t[0] == "v":
        x = t[1]
        return ("bound", bound.index(x)) if x in bound else ("free", x)
    if t[0] == "S":
        return ("S", canonical_term(t[1], bound))
    if t[0] == "I":
        return ("I", canonical_term(t[1], ("u",)),
                canonical_term(t[2], bound), canonical_term(t[3], bound))
    return ("0",)


def canonical(a, bound=()):
    if a[0] == "eq":
        return ("eq", canonical_term(a[1], bound), canonical_term(a[2], bound))
    if a[0] in ("and", "or", "imp"):
        return (a[0], canonical(a[1], bound), canonical(a[2], bound))
    if a[0] in ("all", "ex"):
        return (a[0], canonical(a[2], (a[1],) + bound))
    return ("false",)


def same(a, b):
    return canonical(a) == canonical(b)


def context_vars(context):
    return set().union(*(formula(a) for a in context))


def mask(n, a):
    return ["I", ZERO, n, a]


def infer(p, context):
    """Infer one formula; each recursive call visits a strict proof subtree."""
    require(type(p) is list and bool(p) and type(p[0]) is str)
    rule = p[0]
    if rule == "hyp":
        require(len(p) == 2 and type(p[1]) is int and 0 <= p[1] < len(context))
        return context[p[1]]
    if rule == "refl":
        require(len(p) == 2)
        term(p[1])
        return ["eq", p[1], p[1]]
    if rule == "zero":
        require(len(p) == 3 and term(p[1]) <= {"u"})
        term(p[2])
        return ["eq", ["I", p[1], ZERO, p[2]], p[2]]
    if rule == "step":
        require(len(p) == 4 and term(p[1]) <= {"u"})
        term(p[2])
        term(p[3])
        old = ["I", p[1], p[2], p[3]]
        return ["eq", ["I", p[1], ["S", p[2]], p[3]],
                replace(p[1], {"u": old})]
    if rule == "br":
        require(len(p) == 2)
        term(p[1])
        z = mask(p[1], ONE)
        return ["or", ["eq", z, ZERO], ["eq", z, ONE]]
    if rule == "sep":
        require(len(p) == 1)
        return ["imp", ["eq", ZERO, ONE], ["false"]]
    if rule == "eqE":
        require(len(p) == 5)
        equality = infer(p[1], context)
        require(equality[0] == "eq")
        x = name(p[2])
        formula(p[3])
        require(same(infer(p[4], context), subst(p[3], x, equality[1])))
        return subst(p[3], x, equality[2])
    if rule == "falseE":
        require(len(p) == 3)
        formula(p[1])
        require(infer(p[2], context) == ["false"])
        return p[1]
    if rule == "andI":
        require(len(p) == 3)
        return ["and", infer(p[1], context), infer(p[2], context)]
    if rule == "andE":
        require(len(p) == 3 and type(p[1]) is int and p[1] in (0, 1))
        a = infer(p[2], context)
        require(a[0] == "and")
        return a[p[1] + 1]
    if rule == "orI":
        require(len(p) == 4 and type(p[1]) is int and p[1] in (0, 1))
        formula(p[2])
        a = infer(p[3], context)
        return ["or", a, p[2]] if p[1] == 0 else ["or", p[2], a]
    if rule == "orE":
        require(len(p) == 4)
        a = infer(p[1], context)
        require(a[0] == "or")
        left = infer(p[2], context + [a[1]])
        right = infer(p[3], context + [a[2]])
        require(same(left, right))
        return left
    if rule == "impI":
        require(len(p) == 3)
        formula(p[1])
        return ["imp", p[1], infer(p[2], context + [p[1]])]
    if rule == "impE":
        require(len(p) == 3)
        a = infer(p[1], context)
        require(a[0] == "imp" and same(infer(p[2], context), a[1]))
        return a[2]
    if rule == "allI":
        require(len(p) == 3)
        x = name(p[1])
        require(x not in context_vars(context))
        return ["all", x, infer(p[2], context)]
    if rule == "allE":
        require(len(p) == 3)
        a = infer(p[1], context)
        require(a[0] == "all")
        term(p[2])
        return subst(a[2], a[1], p[2])
    if rule == "exI":
        require(len(p) == 5)
        x = name(p[1])
        formula(p[2])
        term(p[3])
        require(same(infer(p[4], context), subst(p[2], x, p[3])))
        return ["ex", x, p[2]]
    if rule == "exE":
        require(len(p) == 4)
        a = infer(p[1], context)
        require(a[0] == "ex")
        z = name(p[2])
        require(z not in (context_vars(context) | formula(a)))
        result = infer(p[3], context + [subst(a[2], a[1], ["v", z])])
        require(z not in formula(result))
        return result
    if rule == "reset":
        require(len(p) == 6)
        x, f, z, target, premise = p[1:]
        name(x)
        name(z)
        fixed = term(f) - {x}
        require(z != x and z not in (fixed | term(target) | context_vars(context)))
        anchor = replace(f, {x: ONE})
        at_z = replace(f, {x: ["v", z]})
        test = replace(E, {"a": at_z, "b": anchor})
        reset = mask(test, ["S", ["v", z]])
        required = ["eq", replace(f, {x: reset}), anchor]
        require(same(infer(premise, context), required))
        return ["eq", replace(f, {x: target}), anchor]
    raise ValueError("unknown inference rule")


try:
    require(term(E) <= {"a", "b"})
    packet = json.load(open(0))
    require(type(packet) is dict and set(packet) == {"context", "goal", "proof"})
    require(packet["context"] == [])
    require(not formula(packet["goal"]))
    conclusion = infer(packet["proof"], [])
    require(same(conclusion, packet["goal"]))
    print("ACCEPT")
except Exception:
    print("REJECT")
    raise SystemExit(1)
