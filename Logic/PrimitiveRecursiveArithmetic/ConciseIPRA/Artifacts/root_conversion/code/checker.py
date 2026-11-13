"""Raw counter recursion with conversion at the left endpoint only.

Input: {"goal": formula, "proof": proof}; terms use de Bruijn indices.
The eight rule tags are hyp, refl, root, sub, qe, de, di, qi.
No normalizer, semantic evaluator, or axiom oracle is used.
"""

import json
import sys

BIND = {"z": (), "s": (0,), "r": (0, 0, 2),
        "=": (0, 0), "q": (1,), "d": (2,)}
ZERO = ["z"]


def need(condition):
    if not condition:
        raise ValueError("invalid certificate")


def syntax(a, n, formula=False):
    if type(a) is int:
        need(not formula and 0 <= a < n)
        return
    need(type(a) is list and len(a) > 0 and type(a[0]) is str)
    tag = a[0]
    need(tag in BIND and len(a) == len(BIND[tag]) + 1)
    need((tag in ("=", "q", "d")) == formula)
    for child, depth in zip(a[1:], BIND[tag]):
        syntax(child, n + depth, tag in ("q", "d"))


def walk(a, action, depth=0):
    if type(a) is int:
        return action(a, depth)
    return [a[0]] + [walk(b, action, depth + e)
                     for b, e in zip(a[1:], BIND[a[0]])]


def lift(a, amount=1, cutoff=0):
    return walk(a, lambda k, d: k + amount if k >= d + cutoff else k)


def inst(a, images):
    return walk(a, lambda k, d: k if k < d else
                lift(images[k-d], d) if k-d < len(images) else k-len(images))


def root(a):
    if type(a) is not list or a[0] != "r":
        return None
    _, n, seed, body = a
    if n == ZERO:
        return seed
    if type(n) is list and n[0] == "s":
        return inst(body, [["r", n[1], seed, body], n[1]])
    return None


def check(n, context, p):
    need(type(p) is list and len(p) > 0)
    rule, *a = p
    if rule == "hyp":
        i, = a
        need(type(i) is int and 0 <= i < len(context))
        answer = context[i]
    elif rule == "refl":
        t, = a
        syntax(t, n)
        answer = ["=", t, t]
    elif rule == "root":
        t, child = a
        syntax(t, n)
        answer = check(n, context, child)
        need(answer[0] == "=")
        old = answer[1]
        need(root(old) == t or root(t) == old)
        answer = answer.copy()
        answer[1] = t
    elif rule == "sub":
        major, minor = [check(n, context, q) for q in a]
        need(major[0] == minor[0] == "=" and type(major[1]) is int)
        images = list(range(n))
        images[major[1]] = major[2]
        answer = ["=", minor[2], inst(minor[1], images)]
    elif rule == "qe":
        major, minor, t = a
        syntax(t, n)
        major = check(n, context, major)
        need(major[0] == "q")
        need(check(n, context, minor) == inst(major[1], [ZERO]))
        answer = inst(major[1], [t])
    elif rule == "de":
        answer, major, branch = a
        syntax(answer, n, True)
        major = check(n, context, major)
        need(major[0] == "d")
        local = [lift(x) for x in context] + [["q", major[1]]]
        need(check(n+1, local, branch) == lift(answer))
    elif rule == "di":
        body, witness, branch = a
        syntax(body, n+2, True)
        syntax(witness, n)
        base = inst(body, [ZERO, witness])
        step = inst(body, [["s", 0], lift(witness)] + list(range(1, n+1)))
        local = [lift(x) for x in context] + [lift(base)]
        need(check(n+1, local, branch) == step)
        answer = ["d", body]
    elif rule == "qi":
        body, branch = a
        syntax(body, n+1, True)
        need(body[0] == "=")
        step = inst(body, [["s", 0]] + list(range(1, n+1)))
        local = [lift(x) for x in context] + [body]
        need(check(n+1, local, branch) == step)
        answer = ["q", body]
    else:
        raise ValueError("unknown rule")
    syntax(answer, n, True)
    return answer


def main():
    certificate = json.load(sys.stdin)
    need(type(certificate) is dict and set(certificate) == {"goal", "proof"})
    syntax(certificate["goal"], 0, True)
    need(check(0, [], certificate["proof"]) == certificate["goal"])
    print("ACCEPT")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, TypeError, KeyError, IndexError, RecursionError):
        print("REJECT")
        sys.exit(1)
