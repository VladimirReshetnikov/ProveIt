import json
import sys

def require(condition):
    if not condition:
        raise ValueError('invalid certificate')

def walk(a, f, depth=0, form=None):
    if type(a) is int:
        require(form is not True)
        return f(a, depth)
    require(type(a) is list)
    size = len(a)
    require(form is None or (size in ((1, 2) if form else (2, 3)) and (form or size == 3 or a[0] == 0)))
    result = [walk(t, f, depth + (2 if size == 1 else int(size == 3 and i == 2)), None if form is None else size == 1) for i, t in enumerate(a)]
    return result[1] if size == 3 and result[0] == 0 else result

def syntax(a, scope, form=False):

    def variable(i, depth):
        require(-scope <= i <= depth)
        return i
    require(walk(a, variable, form=form) == a)

def opening(a, value, depth=0):
    return walk(a, lambda i, d: value if i == d + 1 else i - (i > d + 1), depth)

def prove(a, p, g):
    n = len(g)
    syntax(a, n, True)
    if len(a) == 2 and a[0] == a[1]:
        return
    match p:
        case ['v', c, b, h, t, major, minor]:
            require(len(a) == 2 and a[1] == opening(h, t))
            prove([b if c == 0 else [c, b, h], t], major, g)
            prove([[[0, c], b, h], a[0]], minor, g)
        case ['u', index, t, premise]:
            require(type(index) is int and 0 <= index < len(g))
            syntax(t, n)
            antecedent, body = g[index]
            require(a == opening(body, t))
            prove(antecedent, premise, g)
        case ['e', body, major, branch]:
            prove([body], major, g)
            body = opening(body, -n - 1, 1)
            prove(a, branch, g + [(opening(body, 0), body)])
        case ['i', t, branch]:
            require(len(a) == 1)
            syntax(t, n)
            body = opening(a[0], t, 1)
            hypothesis = opening(body, -n - 1 if len(a[0]) == 2 and t == 0 else 0)
            prove(opening(body, [0, -n - 1]), branch, g + [([0, 0], hypothesis)])
        case _:
            raise ValueError('invalid proof')

def check(c):
    require(type(c) is dict and set(c) == {'goal', 'proof'})
    prove(c['goal'], c['proof'], [])
if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
