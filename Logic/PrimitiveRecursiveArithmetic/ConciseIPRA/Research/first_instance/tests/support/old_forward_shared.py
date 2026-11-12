import json
import sys


def need(condition):
    if not condition:
        raise ValueError('invalid certificate')


# With a Boolean form, the same traversal validates syntax before reducing.
# Generic traversals receive only checked syntax or constructed iterators.
def walk(a, f, d=0, form=None):
    if type(a) is int:
        need(not form)
        return f(a, d)
    need(type(a) is list)
    size = len(a)
    need(form is None or size in ((1, 2) if form else (2, 3))
            and (form or size == 3 or a[0] == 0))
    a = [walk(b, f, d + (2 if size == 1 else int(size == 3 and i == 2)), size == 1)
         for i, b in enumerate(a)]
    if size == 3:
        c, b, h = a
        if c == 0:
            return b
        if type(c) is list and len(c) == 2:
            # Normalize the predecessor iterate before capture-avoiding insertion.
            return sub(h, walk([c[1], b, h], lambda i, d: i))
    return a


def syntax(a, n, form=False):
    def variable(i, d):
        need(-n <= i <= d)
        return i
    need(walk(a, variable, form=form) == a)


def shift(a, k):
    return walk(a, lambda i, d: i + k if i > d else i)


def sub(a, t, depth=0):
    return walk(a, lambda i, d: shift(t, d) if i == d + 1 else i - (i > d + 1), depth)


def derive(p, g, n):
    match p:
        case ['u', j, t, premise]:
            need(type(j) is int and 0 <= j < len(g))
            syntax(t, n)
            base, body = g[j]
            if base:
                need(derive(premise, g, n) == base)
            a = sub(body, t)
        case ['e', major, eq, branch]:
            body, = derive(major, g, n)
            fresh = -n - 1
            body = sub(body, fresh, 1)
            local = g + [(sub(body, 0), body)]
            equation = derive(eq, local, n + 1)
            need(len(equation) == 2 and equation[0] == fresh)
            a = walk(derive(branch, local, n + 1),
                          lambda i, d: equation[1] if i == fresh else i)
        case ['i', matrix, t, branch]:
            syntax(t, n)
            body = sub(matrix, t, 1)
            hyp = sub(body, -n - 1 if len(body) == 2 and t == 0 else 0)
            need(derive(branch, g + [([], hyp)], n + 1) == sub(body, [0, -n - 1]))
            a = [matrix]
        case _:
            raise ValueError('invalid proof')
    syntax(a, n, True)
    return a


def check(data):
    need(type(data) is dict and set(data) == {'goal', 'proof'})
    syntax(data['goal'], 0, True)
    need(derive(data['proof'], [([], [1, 1])], 0) == data['goal'])


if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
