"""Readable complete checker for S7, the synthesized-introduction calculus.

Terms: 0, free parameter strings, ["v", i], ["s", t], ["i", n, a, h].
The iterator binds one de Bruijn variable in h.  Formulas are ["=", s, t],
["q", B], ["d", B]; q binds one variable and d binds x,y, with y index 0.
Public certificates are [closed_goal, proof].  infer() synthesizes a theorem.
No formula-valued induction and no arithmetic evaluation are trusted.
"""

import json
import sys


class Reject(ValueError):
    pass


def need(condition):
    if not condition:
        raise Reject("invalid certificate")


def integer(value):
    return type(value) is int


def name(value):
    return type(value) is str and bool(value)


def term(t, scope, depth=0):
    if integer(t):
        need(t == 0)
    elif name(t):
        need(t in scope)
    else:
        need(type(t) is list and bool(t))
        op = t[0]
        if op == "v":
            need(len(t) == 2 and integer(t[1]) and 0 <= t[1] < depth)
        elif op == "s":
            need(len(t) == 2)
            term(t[1], scope, depth)
        elif op == "i":
            need(len(t) == 4)
            term(t[1], scope, depth)
            term(t[2], scope, depth)
            term(t[3], scope, depth + 1)
        else:
            raise Reject("unknown term constructor")


def formula(a, scope, depth=0):
    need(type(a) is list and bool(a))
    if a[0] == "=":
        need(len(a) == 3)
        term(a[1], scope, depth)
        term(a[2], scope, depth)
    elif a[0] in ("q", "d"):
        need(len(a) == 2)
        formula(a[1], scope, depth + (1 if a[0] == "q" else 2))
    else:
        raise Reject("unknown formula constructor")


def walk(a, leaf, depth=0):
    """Structural traversal, carrying the number of intervening binders."""
    if type(a) is not list or a[0] == "v":
        return leaf(a, depth)
    if a[0] == "s":
        return ["s", walk(a[1], leaf, depth)]
    if a[0] == "i":
        return ["i", walk(a[1], leaf, depth), walk(a[2], leaf, depth),
                walk(a[3], leaf, depth + 1)]
    if a[0] == "=":
        return ["=", walk(a[1], leaf, depth), walk(a[2], leaf, depth)]
    return [a[0], walk(a[1], leaf, depth + (1 if a[0] == "q" else 2))]


def free(a):
    found = set()

    def collect(t, depth):
        if type(t) is str:
            found.add(t)
        return t

    walk(a, collect)
    return found


def substitute(a, variable, value):
    """Replace a free parameter by a term closed with respect to bound indices."""
    return walk(a, lambda t, depth: value if t == variable else t)


def close(a, variables):
    """Bind free parameter labels, outermost to innermost."""
    n = len(variables)

    def replace(t, depth):
        if type(t) is str and t in variables:
            return ["v", depth + n - 1 - variables.index(t)]
        if type(t) is list and t[0] == "v" and t[1] >= depth:
            return ["v", t[1] + n]
        return t

    return walk(a, replace)


def lift(a, count):
    return walk(a, lambda t, depth: ["v", t[1] + count]
                if type(t) is list and t[0] == "v" and t[1] >= depth else t)


def open_binders(a, values):
    """Simultaneously remove outer binders; values are outermost first."""
    n = len(values)

    def replace(t, depth):
        if type(t) is list and t[0] == "v" and t[1] >= depth:
            index = t[1] - depth
            if index < n:
                return lift(values[n - 1 - index], depth)
            return ["v", t[1] - n]
        return t

    return walk(a, replace)


def replace_term(a, source, target):
    """Root-first, all-occurrence replacement; compare term nodes only.

    source and target have no external bound indices.  Their free parameter
    labels cannot be captured by the locally nameless binders in a.
    """
    if type(a) is not list or a[0] not in ("=", "q", "d"):
        if a == source:
            return target
        if type(a) is not list or a[0] == "v":
            return a
        return [a[0]] + [replace_term(b, source, target) for b in a[1:]]
    return [a[0]] + [replace_term(b, source, target) for b in a[1:]]


def fresh(used):
    i = 0
    while "$" + str(i) in used:
        i += 1
    return "$" + str(i)


def intro_result(witness, eigen, seed, step, scope):
    """The sole introduction rule; the matrix is computed from step."""
    used = scope | free(seed) | free(step) | free(witness) | {eigen}
    x = fresh(used)
    y = fresh(used | {x})
    successor = ["s", eigen]
    if witness == 0 and step[0] == "=":
        body = replace_term(step, successor, y)
        need(eigen not in free(body))
        need(seed == substitute(body, y, eigen))
    else:
        body = replace_term(replace_term(step, witness, x), successor, y)
        need(eigen not in free(body))
        need(seed == substitute(substitute(body, x, witness), y, 0))
    result = ["d", close(body, [x, y])]
    formula(result, scope)
    return result


def infer(proof, context=(), scope=frozenset()):
    need(type(proof) is list and bool(proof))
    op = proof[0]
    if op == "h":
        need(len(proof) == 2 and integer(proof[1]))
        need(0 <= proof[1] < len(context))
        result = context[proof[1]]
    elif op == "z":
        need(len(proof) == 3)
        a, h = proof[1:]
        term(a, scope)
        term(h, scope, 1)
        result = ["=", ["i", 0, a, h], a]
    elif op == "s":
        need(len(proof) == 4)
        n, a, h = proof[1:]
        term(n, scope)
        term(a, scope)
        term(h, scope, 1)
        result = ["=", ["i", ["s", n], a, h],
                  open_binders(h, [["i", n, a, h]])]
    elif op == "t":
        need(len(proof) == 5)
        major, hole, template, minor = proof[1:]
        need(name(hole) and hole not in scope)
        equation = infer(major, context, scope)
        need(equation[0] == "=")
        formula(template, scope | {hole})
        need(template[0] == "=")
        need(infer(minor, context, scope) == substitute(template, hole, equation[1]))
        result = substitute(template, hole, equation[2])
    elif op == "q":
        need(len(proof) == 4)
        major, minor, value = proof[1:]
        term(value, scope)
        closure = infer(major, context, scope)
        need(closure[0] == "q")
        need(infer(minor, context, scope) == open_binders(closure[1], [0]))
        result = open_binders(closure[1], [value])
    elif op == "d":
        need(len(proof) == 4)
        major, eigen, branch = proof[1:]
        need(name(eigen) and eigen not in scope)
        paired = infer(major, context, scope)
        need(paired[0] == "d")
        y = fresh(scope | free(paired) | {eigen})
        opened = open_binders(paired[1], [eigen, y])
        assumption = ["q", close(opened, [y])]
        result = infer(branch, context + (assumption,), scope | {eigen})
        need(eigen not in free(result))
    elif op == "j":
        need(len(proof) == 5)
        witness, eigen, seed, branch = proof[1:]
        term(witness, scope)
        need(name(eigen) and eigen not in scope)
        formula(seed, scope | {eigen})
        step = infer(branch, context + (seed,), scope | {eigen})
        result = intro_result(witness, eigen, seed, step, scope)
    else:
        raise Reject("unknown inference")
    formula(result, scope)
    return result


def verify(certificate):
    need(type(certificate) is list and len(certificate) == 2)
    goal, proof = certificate
    formula(goal, set())
    need(infer(proof) == goal)
    return goal


if __name__ == "__main__":
    try:
        verify(json.load(sys.stdin))
    except (Reject, TypeError, IndexError, KeyError, RecursionError, ValueError):
        sys.exit(1)
    print("ACCEPT")
