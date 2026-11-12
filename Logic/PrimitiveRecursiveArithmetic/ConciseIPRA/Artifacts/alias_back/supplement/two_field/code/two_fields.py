import json


def need(condition):
    if not condition:
        raise ValueError('invalid certificate')


def walk(a, f, d=0, form=None):
    if type(a) is int:
        need(not form)
        return f(a, d)
    need(type(a) is list)
    size = len(a)
    need(form is None or size in ((1, 2) if form else (3,)))
    a = [walk(b, f, d + 2 * (size != 2 and j == size - 1), size == 1)
         for j, b in enumerate(a)]
    if size == 3:
        c, b, h = a
        if c == 0:
            return [0, b, 0]
        if type(c) is list and c[0] == 0:
            return sub(sub(h, c[1], 1), walk([c[1], b, h], lambda i, d: i))
    return a


def syntax(a, n, form=False):
    need(walk(a, lambda i, d: need(1 - n <= i <= d) or i, form=form) == a)


def sub(a, t, depth=0):
    return walk(a, lambda i, d: walk(t, lambda j, e: j + d if j > e else j)
                if i == d + 1 else i - (i > d + 1), depth)


def check(data):
    need(type(data) is list)

    def prove(A, g):
        n = len(g)
        b = -n
        syntax(A, n, True)
        code, arg = data.pop()
        if type(code) is int:
            need(0 <= code < n)
            syntax(arg, n)
            base, B = g[code]
            if base:
                prove(base, g)
            need(sub(B, arg) == A)
        elif code:
            syntax([code], n, True)
            prove([code], g)
            B = sub(code, b, 1)
            base = sub(B, 0)
            row = sub(B, [0, 0, 0])
            prove(arg, g + [(base, B)])
            need(walk(arg, lambda i, d: row[1]
                      if base == [0, 0] and row[0] == i == b else i) == A)
        else:
            need(code == arg == [])
            matrix, = A
            B = sub(matrix, 1 - n, 1)
            base = sub(B, 0)
            hyp = sub(B, b) if base == [0, 0] else base
            prove(sub(B, [0, b, 0]), g + [([], hyp)])

    prove(data.pop(), [([], [1, 1])])
    need(not data)


if __name__ == '__main__':
    check(json.load(open(0)))
    print('ACCEPT')
