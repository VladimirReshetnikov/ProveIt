import json

Z, S, L, R = [0], [1], [2], [3]
ID = []


def require(condition):
    if not condition:
        raise ValueError("invalid certificate")


def word(p):
    if type(p) is not list:
        return False
    for a in p:
        if type(a) is int:
            if a not in range(4):
                return False
        elif type(a) is list and a:
            if a[0] == 4 and type(a[0]) is int and len(a) == 3:
                if not word(a[1]) or not word(a[2]):
                    return False
            elif a[0] == 5 and type(a[0]) is int and len(a) == 2:
                if not word(a[1]):
                    return False
            else:
                return False
        else:
            return False
    return True


def formula(a):
    return (type(a) is list and len(a) == 3 and type(a[0]) is int
            and word(a[1]) and
            (word(a[2]) if a[0] == 0 else
             a[0] in (1, 2) and formula(a[2])))


def fork(p, q):
    return [[4, p, q]]


def iterate(h):
    return [[5, h]]


def eq(p, q):
    return [0, p, q]


def down(a, p):
    return [a[0], p + a[1], p + a[2] if a[0] == 0 else a[2]]


def lift(g):
    return [down(a, R) for a in g]


def arithmetic(tag, args):
    if tag == "C0":
        p, = args
        return eq(p + Z, Z)
    if tag == "CL":
        p, q = args
        return eq(fork(p, q) + L, p)
    if tag == "CR":
        p, q = args
        return eq(fork(p, q) + R, q)
    if tag == "CE":
        p, = args
        return eq(fork(p + L, p + R), p)
    if tag == "P00":
        require(not args)
        return eq(fork(Z, Z), Z)
    if tag == "P0S":
        p, = args
        return eq(fork(Z, p + S), fork(Z, p) + S + S)
    if tag == "PS":
        p, q = args
        return eq(fork(p + S, q), fork(Z, fork(p, q)) + S)
    if tag == "J0":
        a, e, h = args
        return eq(fork(Z, fork(a, e)) + iterate(h), a)
    if tag == "JS":
        n, a, e, h = args
        previous = fork(n, fork(a, e)) + iterate(h)
        return eq(fork(n + S, fork(a, e)) + iterate(h), fork(previous, e) + h)
    raise ValueError("unknown arithmetic axiom")


def check_step(step, history):
    tag, g, a, args, refs = step
    require(type(tag) is str and type(g) is list and all(map(formula, g))
            and formula(a) and type(args) is list and type(refs) is list)
    require(all(type(i) is int and 0 <= i < len(history) for i in refs))
    premises = [history[i] for i in refs]
    if tag == "Hyp":
        require(not args and not refs and a in g)
    elif tag == "Sub":
        w, = args
        require(word(w) and bool(premises))
        delta, b = premises[0]
        require(a == down(b, w) and len(premises) == 1 + len(delta))
        require(all(premises[i + 1] == (g, down(c, w))
                    for i, c in enumerate(delta)))
    elif tag == "Post":
        h, = args
        (g1, e1), (g2, e2) = premises
        require(word(h) and g1 == g2 == g and e1[0] == e2[0] == 0)
        p, q = e1[1:]
        require(e2[1] == p + h and a == eq(e2[2], q + h))
    elif tag == "Pair":
        (g1, e1), (g2, e2) = premises
        require(not args and g1 == g2 == g and e1[0] == e2[0] == 0)
        require(a == eq(fork(e1[1], e2[1]), fork(e1[2], e2[2])))
    elif tag == "Transport":
        b, = args
        (g1, e), (g2, c) = premises
        require(formula(b) and g1 == g2 == g and e[0] == 0)
        require(c == down(b, e[1]) and a == down(b, e[2]))
    elif tag == "QE":
        t, = args
        (g1, q), (g2, base) = premises
        require(word(t) and g1 == g2 == g and q[0] == 1)
        p, b = q[1:]
        require(base == down(b, fork(Z, p)) and a == down(b, fork(t, p)))
    elif tag == "DE":
        (g1, d), (g2, result) = premises
        require(not args and g1 == g and d[0] == 2)
        p, b = d[1:]
        opened = [1, fork(L, R + p), b]
        require(g2 == lift(g) + [opened] and result == down(a, R))
    elif tag == "DI":
        t, = args
        (g1, result), = premises
        require(word(t) and a[0] == 2)
        p, b = a[1:]
        q = fork(t, p)
        base = down(b, fork(Z, R + q))
        following = down(b, fork(L + S, R + q))
        require(g1 == lift(g) + [base] and result == following)
    elif tag == "QI":
        (g1, result), = premises
        require(not args and a[0] == 1)
        p, b = a[1:]
        base = down(b, fork(Z, R + p))
        following = down(b, fork(L + S, R + p))
        require(g1 == lift(g) + [base] and result == following)
    elif tag == "Ind":
        (g1, result), = premises
        require(not args and a[0] == 1 and a[2][0] == 0)
        p, e = a[1:]
        base = down(e, fork(L, R + p))
        following = down(e, fork(L + S, R + p))
        require(g1 == lift(g) + [base] and result == following)
    else:
        require(not refs and all(map(word, args)))
        require(a == arithmetic(tag, args))
    return g, a


def verify(data):
    require(type(data) is list and bool(data))
    history = []
    for step in data:
        require(type(step) is list and len(step) == 5)
        history.append(check_step(step, history))
    require(history[-1][0] == [])
    return history[-1][1]


if __name__ == "__main__":
    verify(json.load(open(0)))
    print("ACCEPT")
