#!/usr/bin/env python3
"""Nine-equation cyclic presentation of Df3 and a complete rewrite kernel.

New reference implementation, 2026-10-17. MIT-0.
This is not a binary Turing machine or a compiled ZFC-specific target.
Terms are immutable prefix trees. Schema leaves x,y,z are metavariables;
the one generator p is a literal constant, never a substitution variable.
"""
from __future__ import annotations

from itertools import product
from math import isqrt


P = ("p",)
X, Y, Z = ("x",), ("y",), ("z",)
VARIABLES = {"x", "y", "z"}
UNARY = ("n", "c", "r")


def natural(n):
    return type(n) is int and n >= 0


def require_natural(n):
    if not natural(n):
        raise ValueError("expected an exact nonnegative integer")


def ground_term(t):
    """Validate public AST input, including exact arities and literal p."""
    if type(t) is not tuple or not t or type(t[0]) is not str:
        return False
    if t == P:
        return True
    if t[0] in UNARY:
        return len(t) == 2 and ground_term(t[1])
    if t[0] == "j":
        return len(t) == 3 and ground_term(t[1]) and ground_term(t[2])
    return False


def valid_step(step, invariant=False):
    if type(step) not in (tuple, list) or len(step) != 4:
        return False
    rule, reverse, path, witness = step
    return (natural(rule) and rule < (10 if invariant else 9)
            and type(reverse) is bool and type(path) in (tuple, list)
            and all(type(a) is int and a in (0, 1) for a in path)
            and ground_term(witness))


def neg(a): return ("n", a)
def close(a): return ("c", a)
def rotate(a): return ("r", a)
def join(a, b): return ("j", a, b)


# Juxtaposition in the report means composition, rightmost operation first.
BASIS = (
    ("B1", join(X, Y), join(Y, X)),
    ("B2", join(X, join(Y, Z)), join(join(X, Y), Z)),
    ("B3", neg(join(neg(join(X, Y)), neg(join(X, neg(Y))))), X),
    ("C1", join(X, close(X)), close(X)),
    ("C2", close(join(X, Y)), join(close(X), close(Y))),
    ("C3", close(neg(close(X))), neg(close(X))),
    ("R1", rotate(join(X, Y)), join(rotate(X), rotate(Y))),
    ("R2", rotate(rotate(rotate(X))), X),
    ("M", close(rotate(close(X))),
     rotate(close(rotate(rotate(close(rotate(X))))))),
)


def variables(t):
    if t[0] in VARIABLES:
        return {t[0]}
    return set().union(*(variables(x) for x in t[1:]))


def substitute(t, env):
    if t[0] in VARIABLES:
        return env[t[0]]
    return (t[0], *(substitute(x, env) for x in t[1:]))


def match(pattern, term, env):
    """Match fixed axiom pattern; repetitions must match exactly."""
    if pattern[0] in VARIABLES:
        key = pattern[0]
        if key in env:
            return env[key] == term
        env[key] = term
        return True
    return (len(pattern) == len(term) and pattern[0] == term[0]
            and all(match(a, b, env) for a, b in zip(pattern[1:], term[1:])))


def rewrite(term, rule, reverse=False, path=(), witness=P, invariant=False):
    """One contextual rewrite, or None for an invalid match/address.

    The only regular orientation introducing an unbound variable is B3
    backwards; its y is supplied by witness. Optional rule 9 is the GROUND
    equation r(p)=p and is deliberately outside the schema matcher.
    """
    if path:
        child = path[0]
        if child not in (0, 1) or child + 1 >= len(term):
            return None
        changed = rewrite(term[child + 1], rule, reverse, path[1:], witness,
                          invariant)
        if changed is None:
            return None
        children = list(term[1:])
        children[child] = changed
        return (term[0], *children)
    if rule == 9 and invariant:
        left, right = (rotate(P), P)
    elif 0 <= rule < 9:
        _, left, right = BASIS[rule]
    else:
        return None
    if reverse:
        left, right = right, left
    env = {}
    if not match(left, term, env):
        return None
    for missing in variables(right) - set(env):
        # BASIS has just the one missing variable (B3 backwards: y).
        env[missing] = witness
    return substitute(right, env)


def check(start, goal, script, invariant=False):
    """Validated public checker; entries: (rule, reverse, address, witness)."""
    if type(invariant) is not bool or not ground_term(start) or not ground_term(goal):
        return False
    current = start
    try:
        for step in script:
            if not valid_step(step, invariant):
                return False
            rule, reverse, path, witness = step
            current = rewrite(current, rule, reverse, path, witness, invariant)
            if current is None:
                return False
    except (TypeError, ValueError, KeyError, IndexError):
        return False
    return current == goal


def pair(a, b):
    require_natural(a)
    require_natural(b)
    s = a + b
    return s * (s + 1) // 2 + b


def unpair(n):
    require_natural(n)
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def term_decode(n):
    """Every natural number is a ground term; every ground term has a code."""
    require_natural(n)
    if n == 0:
        return P
    q, tag = divmod(n - 1, 4)
    if tag < 3:
        return (UNARY[tag], term_decode(q))
    a, b = unpair(q)
    return join(term_decode(a), term_decode(b))


def term_encode(t):
    if not ground_term(t):
        raise ValueError("not a ground term over the specified signature")
    if t == P:
        return 0
    if t[0] in UNARY:
        return 4 * term_encode(t[1]) + UNARY.index(t[0]) + 1
    if t[0] == "j":
        return 4 * pair(term_encode(t[1]), term_encode(t[2])) + 4
    raise ValueError("not a ground term over the specified signature")


def path_decode(n):
    require_natural(n)
    return tuple(int(b) for b in bin(n + 1)[3:])


def path_encode(path):
    if (type(path) not in (tuple, list)
            or not all(type(a) is int and a in (0, 1) for a in path)):
        raise ValueError("expected a sequence of exact 0/1 address bits")
    return int("1" + "".join(map(str, path)), 2) - 1


def step_decode(n, invariant=False):
    require_natural(n)
    if type(invariant) is not bool:
        raise ValueError("expected an exact Boolean option")
    payload, tag = divmod(n, 20 if invariant else 18)
    path, witness = unpair(payload)
    return tag // 2, bool(tag % 2), path_decode(path), term_decode(witness)


def step_encode(step, invariant=False):
    if type(invariant) is not bool or not valid_step(step, invariant):
        raise ValueError("invalid rewrite step")
    rule, reverse, path, witness = step
    return ((20 if invariant else 18)
            * pair(path_encode(path), term_encode(witness)) + 2 * rule + reverse)


def list_decode(n):
    require_natural(n)
    while n:
        head, n = unpair(n - 1)
        yield head


def list_encode(items):
    result = 0
    for item in reversed(items):
        require_natural(item)
        result = 1 + pair(item, result)
    return result


def check_code(start, goal, code, invariant=False):
    if not natural(code):
        return False
    return check(start, goal,
                 (step_decode(n, invariant) for n in list_decode(code)), invariant)


def search(start, goal, invariant=False):
    """Ideal fair exhaustive search. Terminates exactly on E9 consequences.

    Concrete Python execution is subject to memory/stack limits; the total
    finite-tree predicate and fairness are statements about the ideal search.
    """
    if type(invariant) is not bool or not ground_term(start) or not ground_term(goal):
        raise ValueError("search requires ground E9 endpoints and a Boolean option")
    candidate = 0
    while True:
        if check_code(start, goal, candidate, invariant):
            return candidate
        candidate += 1


def translate(t):
    """Df3 symbols f,g,h map to c,r c r^2,r^2 c r."""
    kind = t[0]
    args = tuple(translate(a) for a in t[1:])
    if kind == "f": return close(args[0])
    if kind == "g": return rotate(close(rotate(rotate(args[0]))))
    if kind == "h": return rotate(rotate(close(rotate(args[0]))))
    return (kind, *args)


def tree_size(t):
    return 1 + sum(map(tree_size, t[1:]))


def prefix(t):
    return t[0] + "".join(map(prefix, t[1:]))


def df18():
    result = list(BASIS[:3])
    for F in ("f", "g", "h"):
        op = lambda a: (F, a)
        result.extend((
            (F + "1", join(X, op(X)), op(X)),
            (F + "2", op(op(X)), op(X)),
            (F + "3", op(join(X, Y)), join(op(X), op(Y))),
            (F + "4", op(neg(op(X))), neg(op(X))),
        ))
    for F, G in (("f", "g"), ("f", "h"), ("g", "h")):
        result.append((F + G, (F, (G, X)), (G, (F, X))))
    return result


def fold_to_root8(t):
    """Replace n by s^3 and r by s^2; E8 recovers E9 definitionally."""
    args = tuple(fold_to_root8(a) for a in t[1:])
    if t[0] == "n":
        return ("s", ("s", ("s", args[0])))
    if t[0] == "r":
        return ("s", ("s", args[0]))
    return (t[0], *args)


def unfold_from_root8(t):
    """Interpret s as n r^2 in E9."""
    args = tuple(unfold_from_root8(a) for a in t[1:])
    if t[0] == "s":
        return neg(rotate(rotate(args[0])))
    return (t[0], *args)


def root8():
    return [(name, fold_to_root8(a), fold_to_root8(b))
            for name, a, b in BASIS if name != "R2"]


def metrics():
    def measure(rows):
        lengths = [tree_size(a) + tree_size(b) for _, a, b in rows]
        return {"equations": len(rows), "tree_nodes": sum(lengths),
                "row_tree_nodes": lengths,
                "prefix_sides": [[prefix(a), prefix(b)] for _, a, b in rows]}
    return {"Df3_18": measure(df18()),
            "Df3_15_without_idempotence": measure(
                [row for row in df18() if row[0] not in ("f2", "g2", "h2")]),
            "rotation_9": measure(BASIS),
            "root_8": measure(root8()),
            "not_measured": ["compiled_ZFC_target", "binary_TM_states",
                             "decoder", "bootstrap", "runtime"]}


def evaluate(t, env, operations):
    if len(t) == 1:
        return env[t[0]]
    return operations[t[0]](*(evaluate(a, env, operations) for a in t[1:]))


def validate_algebra(rows, domain, operations):
    """Exhaustive finite check, returning first failure or None."""
    for name, left, right in rows:
        names = sorted(variables(left) | variables(right))
        for values in product(domain, repeat=len(names)):
            env = dict(zip(names, values))
            if evaluate(left, env, operations) != evaluate(right, env, operations):
                return {"row": name, "valuation": env}
    return None


if __name__ == "__main__":
    import json
    print(json.dumps(metrics(), indent=2))
