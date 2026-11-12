"""Standalone iPRA checker with equality at witness discharge.

There are three proof instructions: u (optional-premise clause use),
i (paired introduction), e (paired elimination with equality substitution).
Every proof begins with the explicit unconditional clause forall y, y=y.
Terms and formulas are full computation normal forms. Integer 0 is zero;
negative integers are free levels, positive integers are bound indices;
[0,t] is successor, [n,a,h] is iteration, [s,t] is equality, [B] binds two.

Input is exactly a JSON object with goal, proof, and fuel fields. Goals are closed.
The premise payload of unconditional u is intentionally ignored; use null.
Only this file and the Python standard library are needed for acceptance.
Exceptions reject; ACCEPT is printed only after the entire goal is checked.
"""
import json
import sys


def need(condition):
    if not condition:
        raise ValueError('invalid certificate')


# With a Boolean form, the same traversal validates syntax before reducing.
# Generic traversals receive only checked syntax or constructed iterators.
def spend():
    global remaining
    remaining -= 1
    need(remaining >= 0)


def walk(a, f, d=0, form=None):
    spend()
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


def prove(a, p, g, n):
    spend()
    syntax(a, n, True)
    match p:
        case ['u', j, t, premise]:
            need(type(j) is int and 0 <= j < len(g))
            syntax(t, n)
            base, body = g[j]
            need(a == sub(body, t))
            # Empty antecedent means no logical premise. The payload is unused.
            if base:
                prove(base, premise, g, n)
        case ['e', body, fml, t, major, eq, branch]:
            prove([body], major, g, n)
            body = sub(body, -n - 1, 1)
            local = g + [(sub(body, 0), body)]
            prove([-n - 1, t], eq, local, n + 1)
            prove(fml, branch, local, n + 1)
            # t is canonical and has no loose bound indices, by its equality proof.
            # An inserted copy is not visited again. Outer goal a excludes the name.
            need(walk(fml, lambda i, d: t if i == -n - 1 else i) == a)
        case ['i', t, branch]:
            need(len(a) == 1)
            syntax(t, n)
            body = sub(a[0], t, 1)
            hyp = sub(body, -n - 1 if len(body) == 2 and t == 0 else 0)
            prove(sub(body, [0, -n - 1]), branch, g + [([], hyp)], n + 1)
        case _:
            raise ValueError('invalid proof')


def check(data):
    global remaining
    need(type(data) is dict and set(data) == {'goal', 'proof', 'fuel'})
    remaining = data['fuel']
    need(type(remaining) is int and remaining >= 0)
    prove(data['goal'], data['proof'], [([], [1, 1])], 0)


if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
