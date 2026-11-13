import json
import sys


if not __debug__:
    raise RuntimeError('Run this checker without -O')


def term(a, n):
    if type(a) is int:
        return 0 <= a <= n
    return type(a) is list and (
        len(a) == 1 and term(a[0], n)
        or len(a) == 3 and term(a[0], n) and term(a[1], n)
        and term(a[2], n + 1))


def formula(a, n):
    return type(a) is list and (
        len(a) == 1 and formula(a[0], n + 2)
        or len(a) == 2 and term(a[0], n) and term(a[1], n))


def walk(a, action, f=False, depth=0):
    if type(a) is int:
        return action(a, depth)
    if f and len(a) == 1:
        return [walk(a[0], action, True, depth + 2)]
    return [walk(x, action, False, depth + (len(a) == 3 and j == 2))
            for j, x in enumerate(a)]


def lift(a, count=1, f=False, cutoff=0):
    return walk(a, lambda i, d: i + count if i > d + cutoff else i, f)


def instance(a, args, f=False, extra=0):
    def replace(i, d):
        if i <= d:
            return i
        j = i - d
        if j <= len(args):
            return lift(args[j - 1], d)
        return i - len(args) + extra
    return walk(a, replace, f)


def export(a):
    def remove(i, d):
        assert i != d + 1
        return i - (i > d + 1)
    return walk(a, remove, True)


def gate(a):
    def build(b, depth=0):
        if len(b) == 1:
            return [build(b[0], depth + 2)]
        s, t = b
        return [[0, s, lift(t)], [depth + 1, s, lift(t)]]
    return build(lift(a, f=True))


def reflexive(a):
    while len(a) == 1:
        a = a[0]
    return a[0] == a[1]


def diagonal(b):
    return len(b) == 2 and all(
        type(t) is list and len(t) == 3 and t[:2] == [1, 1]
        for t in b)


def step(e, f):
    assert len(e) == len(f) == 2
    s, t = e
    b, r = f
    assert type(b) is list and len(b) == 3
    c, a, h = b
    if c == 0:
        assert a == s
        return [r, t]
    assert type(c) is list and len(c) == 1 and s == [c[0], a, h]
    return [r, instance(h, [t])]


def branch_context(context, body):
    return [lift(c, f=True, cutoff=1) for c in context] + [body]


def check(p, n=0, context=None):
    if context is None:
        context = [[1, 1]]
    assert type(p) is list and p
    tag = p[0]
    if tag == 'use':
        assert len(p) == 4
        _, index, t, q = p
        assert type(index) is int and 0 <= index < len(context) and term(t, n)
        body = context[index]
        base = instance(body, [0], True)
        assert q is None and reflexive(base) or check(q, n, context) == base
        return instance(body, [t], True)
    if tag == 'intro':
        assert len(p) == 4
        _, a, t, q = p
        assert formula(a, n) and len(a) == 1 and term(t, n)
        body = a[0]
        seed = instance(body, [int(diagonal(body)), lift(t)], True, 1)
        target = instance(body, [[1], lift(t)], True, 1)
        assert check(q, n + 1, branch_context(context, gate(seed))) == target
        return a
    assert tag == 'discharge' and len(p) == 4
    major = check(p[1], n, context)
    assert len(major) == 1
    extended = branch_context(context, major[0])
    e, f = [check(q, n + 1, extended) for q in p[2:]]
    return export(f if len(e) == 1 else step(e, f))


def accepts(document):
    try:
        goal, certificate = document
        return formula(goal, 0) and check(certificate) == goal
    except (AssertionError, IndexError, TypeError, ValueError, RecursionError):
        return False


if __name__ == '__main__':
    try:
        print(accepts(json.load(sys.stdin)))
    except (ValueError, TypeError):
        print(False)
