import json
import sys

def need(condition):
    if not condition:
        raise ValueError('invalid certificate')
fuel = 0

def tick():
    global fuel
    need(fuel > 0)
    fuel -= 1

def walk(a, f, d=0, form=None):
    tick()
    if type(a) is int:
        need(not form)
        return f(a, d)
    need(type(a) is list)
    size = len(a)
    need(form is None or (size in ((1, 2) if form else (2, 3)) and (form or size == 3 or a[0] == 0)))
    a = [walk(b, f, d + (2 if size == 1 else int(size == 3 and i == 2)), size == 1) for i, b in enumerate(a)]
    if size == 3:
        c, b, h = a
        if c == 0:
            return b
        if type(c) is list and len(c) == 2:
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

def derive(packet, g):
    tick()
    n = len(g)
    code, arg, branch = packet
    if type(code) is int:
        need(0 <= code < len(g))
        syntax(arg, n - 1)
        base, body = g[code]
        if base:
            need(derive(branch, g) == base)
        a = sub(body, arg)
    elif code:
        syntax(arg, n - 1)
        body = sub(code, arg, 1)
        hyp = sub(body, -n if len(body) == 2 and arg == 0 else 0)
        need(derive(branch, g + [([], hyp)]) == sub(body, [0, -n]))
        a = [code]
    else:
        need(code == [])
        body, = derive(arg, g)
        body = sub(body, -n, 1)
        base = sub(body, 0)
        local = g + [(base, body)]
        equality, branch = branch
        source, target = derive(equality, local)
        need(source == -n)
        a = walk(derive(branch, local), lambda i, d: target if i == -n else i)
    syntax(a, n - 1, True)
    return a

def check(data):
    global fuel
    need(type(data) is dict and set(data) == {'goal', 'proof', 'fuel'})
    fuel = data['fuel']
    need(type(fuel) is int and fuel >= 0)
    syntax(data['goal'], 0, True)
    need(derive(data['proof'], [([], [1, 1])]) == data['goal'])
if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
