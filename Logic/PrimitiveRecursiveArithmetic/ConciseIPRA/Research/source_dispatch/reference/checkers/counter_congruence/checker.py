"""Standalone checker for iPRA with root replacement and counter congruence.

This is a readable new implementation, not a claim of a smaller source kernel.
JSON is data only. All arithmetic, logic, scoping, substitution, and the public
ACCEPT/REJECT driver are in this file; only Python's standard json is imported.
See FORMAT.txt for the complete mathematical and serialization contract.
"""
import json


class Invalid(Exception):
    pass


def require(condition, message):
    if not condition:
        raise Invalid(message)


def term(raw, free, bound=()):
    require(type(raw) is list and bool(raw), "A term must be a tagged array")
    tag = raw[0]
    if tag == "0":
        require(len(raw) == 1, "Zero arity")
        return ("0",)
    if tag == "v":
        require(len(raw) == 2 and type(raw[1]) is str, "Variable arity")
        name = raw[1]
        if name in bound:
            return ("b", bound.index(name))
        require(name in free, "Unbound numerical variable: " + name)
        return ("f", name)
    if tag == "S":
        require(len(raw) == 2, "Successor arity")
        return ("S", term(raw[1], free, bound))
    if tag == "R":
        require(len(raw) == 6, "Recursor arity")
        _, n, a, u, v, h = raw
        require(type(u) is str and type(v) is str and u != v,
                "Distinct numerical binders required")
        return ("R", term(n, free, bound), term(a, free, bound),
                term(h, free, (v, u) + bound))
    raise Invalid("Unknown numerical constructor")


def formula(raw, free, bound=(), internal=False):
    require(type(raw) is list and bool(raw), "A formula must be a tagged array")
    tag = raw[0]
    if tag == "=":
        require(len(raw) == 3, "Equation arity")
        return ("=", term(raw[1], free, bound), term(raw[2], free, bound))
    if tag == "D":
        require(len(raw) == 4, "Paired binder arity")
        _, x, y, body = raw
        require(type(x) is str and type(y) is str and x != y,
                "Distinct paired binders required")
        return ("D", formula(body, free, (y, x) + bound))
    if tag == "Q":
        require(internal and len(raw) == 3 and type(raw[1]) is str,
                "Q is an internal clause, not an object constructor")
        return ("Q", formula(raw[2], free, (raw[1],) + bound))
    raise Invalid("Unknown formula constructor")


def walk(tree, variable, depth=0):
    """Walk both sorts, charging each binder only to its actual body."""
    tag = tree[0]
    if tag == "b":
        return variable(tree[1], depth)
    if tag in ("0", "f"):
        return tree
    if tag == "R":
        return (tag, walk(tree[1], variable, depth),
                walk(tree[2], variable, depth),
                walk(tree[3], variable, depth + 2))
    if tag in ("D", "Q"):
        return (tag, walk(tree[1], variable, depth + (2 if tag == "D" else 1)))
    return (tag,) + tuple(walk(child, variable, depth) for child in tree[1:])


def shift(tree, amount):
    return walk(tree, lambda index, depth:
                ("b", index + amount if index >= depth else index))


def substitute(tree, index, image):
    """Remove one enclosing binder, replacing its coordinate by image."""
    def variable(current, depth):
        if current == index + depth:
            return shift(image, depth)
        return ("b", current - (current > index + depth))
    return walk(tree, variable)


ZERO = ("0",)


def fresh(proof, free):
    name = proof["eigen"]
    require(type(name) is str and name not in free,
            "The eigenparameter must be fresh")
    return ("f", name), free | {name}


def check(goal, proof, context, free):
    require(type(proof) is dict, "A proof node must be an object")
    rule = proof["rule"]
    require(goal[0] != "Q" or rule == "hyp",
            "An internal closure is available only by context membership")

    if rule == "hyp":
        index = proof["index"]
        require(type(index) is int and 0 <= index < len(context),
                "Hypothesis index out of range")
        require(context[index] == goal, "Hypothesis does not match the goal")
        return

    if rule in ("R0", "RS"):
        require(goal[0] == "=" and goal[1][0] == "R",
                "Computation must conclude a recursor equation")
        _, n, a, h = goal[1]
        if rule == "R0":
            require(n == ZERO, "R0 has a nonzero counter")
            expected = ("S", a)
        else:
            require(n[0] == "S", "RS needs a displayed successor")
            predecessor = n[1]
            recursive = ("R", predecessor, a, h)
            expected = substitute(substitute(h, 1, predecessor), 0, recursive)
        require(goal[2] == expected, "Wrong computation result")
        return

    if rule == "RL":
        major = formula(proof["equality"], free)
        require(major[0] == "=" and goal[0] == "=", "RL requires equations")
        check(major, proof["major"], context, free)
        require(goal[1] == major[2], "RL target endpoint mismatch")
        check(("=", major[1], goal[2]), proof["minor"], context, free)
        return

    if rule == "CC":
        require(goal[0] == "=" and goal[1][0] == goal[2][0] == "R",
                "CC requires recursors at both equation roots")
        left, right = goal[1:]
        require(left[2:] == right[2:], "CC may change only the counter")
        check(("=", left[1], right[1]), proof["major"], context, free)
        return

    if rule == "QE":
        major = formula(proof["closure"], free, internal=True)
        require(major[0] == "Q", "QE needs an internal closure")
        target = term(proof["target"], free)
        require(goal == substitute(major[1], 0, target), "QE target mismatch")
        check(major, proof["major"], context, free)
        check(substitute(major[1], 0, ZERO), proof["base"], context, free)
        return

    if rule == "DE":
        major = formula(proof["paired"], free)
        require(major[0] == "D", "DE needs a paired formula")
        check(major, proof["major"], context, free)
        eigen, extended = fresh(proof, free)
        clause = ("Q", substitute(major[1], 1, eigen))
        check(goal, proof["body"], context + [clause], extended)
        return

    if rule == "DI":
        require(goal[0] == "D", "DI needs a paired goal")
        witness = term(proof["witness"], free)
        matrix = substitute(goal[1], 1, witness)
        mode = proof["mode"]
        require(mode in ("case", "progress"), "Unknown DI mode")
        require(mode == "case" or matrix[0] == "=",
                "Progress introduction requires a literal equation")
        eigen, extended = fresh(proof, free)
        previous = eigen if mode == "progress" else ZERO
        hypothesis = substitute(matrix, 0, previous)
        step = substitute(matrix, 0, ("S", eigen))
        check(step, proof["body"], context + [hypothesis], extended)
        return

    raise Invalid("Unknown inference rule")


def verify(packet):
    require(type(packet) is dict, "The certificate must be an object")
    parameters = packet.get("parameters", [])
    require(type(parameters) is list and all(type(x) is str for x in parameters),
            "Parameters must be a list of names")
    require(len(parameters) == len(set(parameters)), "Repeated free parameter")
    free = set(parameters)
    goal = formula(packet["goal"], free)
    check(goal, packet["proof"], [], free)
    return True


if __name__ == "__main__":
    try:
        verify(json.load(open(0)))
    except Exception as error:
        print("REJECT")
        raise SystemExit(str(error))
    print("ACCEPT")

