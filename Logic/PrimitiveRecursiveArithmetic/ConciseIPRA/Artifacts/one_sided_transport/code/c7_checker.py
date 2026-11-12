# Standalone strict proof checker; its equality branch determines the calculus.
# JSON input is [closed_formula, proof]. Success prints ACCEPT.
# Variables are de Bruijn levels: 0,...,n-1 in a context of size n.
# Terms: integer variable, ["0"], ["S",t], ["I",n,a,h].
# Only h binds a variable; its level is the ambient context size.
# Formulas: ["=",s,t], ["Q",B], ["D",B].
# Q binds y; D binds x then y, in that order.
import json

ZERO = ["0"]


def require(condition):
    if not condition:
        raise ValueError("Invalid certificate")


def term(a, n):
    if type(a) is int:
        return 0 <= a < n
    if type(a) is not list or not a:
        return False
    return (a == ZERO or
            len(a) == 2 and a[0] == "S" and term(a[1], n) or
            len(a) == 4 and a[0] == "I" and
            term(a[1], n) and term(a[2], n) and term(a[3], n + 1))


def formula(a, n):
    if type(a) is not list or not a:
        return False
    return (len(a) == 3 and a[0] == "=" and
            term(a[1], n) and term(a[2], n) or
            len(a) == 2 and a[0] == "Q" and formula(a[1], n + 1) or
            len(a) == 2 and a[0] == "D" and formula(a[1], n + 2))


def lift(a, n, amount=1):
    # Insert numerical parameters at level n, including under binders.
    if type(a) is int:
        return a + amount * (a >= n)
    return [a[0]] + [lift(b, n, amount) for b in a[1:]]


def replace(a, n, t, remove=True, depth=None):
    # All internal binders of a are above n. With remove=False,
    # the level n remains allocated as a fresh numerical parameter.
    if depth is None:
        depth = n + 1
    if type(a) is int:
        return (lift(t, n + (not remove), depth - n - 1)
                if a == n else a - (remove and a > n))
    return [a[0]] + [
        replace(b, n, t, remove,
                depth + (2 if a[0] == "D" else
                         int(a[0] == "Q" or a[0] == "I" and j == 3)))
        for j, b in enumerate(a[1:], 1)]


def check(a, p, context=(), n=0):
    require(formula(a, n) and type(p) is list and p)
    op = p[0]
    if op == "hyp":
        require(len(p) == 2 and type(p[1]) is int and
                0 <= p[1] < len(context) and context[p[1]] == a)
    elif op == "i0":
        require(len(p) == 3)
        b, h = p[1:]
        require(term(b, n) and term(h, n + 1) and
                a == ["=", ["I", ZERO, b, h], b])
    elif op == "is":
        require(len(p) == 4)
        v, b, h = p[1:]
        require(term(v, n) and term(b, n) and term(h, n + 1))
        require(a == ["=", ["I", ["S", v], b, h],
                      replace(h, n, ["I", v, b, h])])
    elif op == "x":
        require(len(p) == 6 and a[0] == "=")
        s, t, f, major, minor = p[1:]
        require(term(s, n) and s != ZERO and term(t, n) and
                term(f, n + 1) and a[2] == replace(f, n, t))
        check(["=", s, t], major, context, n)
        check(["=", replace(f, n, s), a[1]], minor, context, n)
    elif op == "qe":
        require(len(p) == 5)
        b, t, major, minor = p[1:]
        require(formula(b, n + 1) and term(t, n) and
                a == replace(b, n, t))
        check(["Q", b], major, context, n)
        check(replace(b, n, ZERO), minor, context, n)
    elif op == "de":
        require(len(p) == 4)
        b, major, continuation = p[1:]
        require(formula(b, n + 2))
        check(["D", b], major, context, n)
        check(lift(a, n), continuation,
              tuple(lift(g, n) for g in context) + (["Q", b],), n + 1)
    elif op == "di":
        require(len(p) == 3 and a[0] == "D" and term(p[1], n))
        b = replace(a[1], n, p[1], depth=n + 2)
        seed = n if a[1][0] == "=" and p[1] == ZERO else ZERO
        assumption = replace(b, n, seed, False)
        conclusion = replace(b, n, ["S", n], False)
        check(conclusion, p[2],
              tuple(lift(g, n) for g in context) + (assumption,), n + 1)
    else:
        raise ValueError("Unknown rule")


if __name__ == "__main__":
    certificate = json.load(open(0))
    require(type(certificate) is list and len(certificate) == 2)
    check(*certificate)
    print("ACCEPT")
