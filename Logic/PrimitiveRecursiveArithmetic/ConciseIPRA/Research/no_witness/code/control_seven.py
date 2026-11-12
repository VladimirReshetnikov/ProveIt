import json

def require(condition):
    if not condition:
        raise ValueError('Invalid certificate')

def term(a, n, d=0):
    if type(a) is int:
        return -n <= a <= d
    return type(a) is list and len(a) in (2, 3) and (len(a) == 3 or a[0] == 0) and all((term(b, n, d + int(len(a) == 3 and j == 2)) for j, b in enumerate(a)))

def formula(a, n, d=0):
    if type(a) is not list:
        return False
    if len(a) == 1:
        return formula(a[0], n, d + 2)
    if len(a) == 2 and a[0] == 'q':
        return formula(a[1], n, d + 1)
    return len(a) == 2 and all((term(b, n, d) for b in a))

def opening(a, t, d=0):
    if type(a) is int:
        return t if a == d + 1 else a - int(a > d + 1)
    if a[0] == 'q':
        return ['q', opening(a[1], t, d + 1)]
    return [opening(b, t, d + (2 if len(a) == 1 else int(len(a) == 3 and j == 2))) for j, b in enumerate(a)]

def infer(p, g, n):
    match p:
        case ['hyp', j]:
            require(type(j) is int and 0 <= j < len(g))
            return g[j]
        case ['zero', a, h]:
            require(term(a, n) and term(h, n, 1))
            return [[0, a, h], a]
        case ['succ', c, a, h]:
            require(term(c, n) and term(a, n) and term(h, n, 1))
            return [[[0, c], a, h], opening(h, [c, a, h])]
        case ['tr', h, p, q]:
            require(term(h, n, 1))
            s, t = infer(p, g, n)
            b, r = infer(q, g, n)
            require(s != 'q' and b != 'q' and (b == opening(h, s)))
            return [r, opening(h, t)]
        case ['qe', t, p, q]:
            require(term(t, n))
            k, b = infer(p, g, n)
            require(k == 'q' and infer(q, g, n) == opening(b, 0))
            return opening(b, t)
        case ['de', a, p, q]:
            require(formula(a, n))
            b, = infer(p, g, n)
            require(infer(q, g + [['q', opening(b, -n - 1, 1)]], n + 1) == a)
            return a
        case ['di', b, t, p]:
            require(formula(b, n, 2) and term(t, n))
            a = opening(b, t, 1)
            match b:
                case [[1, 1, _], [1, 1, _]]:
                    eta = -n - 1
                case _:
                    eta = 0
            require(infer(p, g + [opening(a, eta)], n + 1) == opening(a, [0, -n - 1]))
            return [b]
        case _:
            raise ValueError('Invalid proof')

def check(c):
    require(type(c) is dict and set(c) == {'variables', 'context', 'goal', 'proof'})
    n, g, a, p = (c[k] for k in ['variables', 'context', 'goal', 'proof'])
    require(type(n) is int and n >= 0 and (type(g) is list))
    require(all((formula(b, n) for b in g)) and formula(a, n))
    require(infer(p, g, n) == a)
if __name__ == '__main__':
    check(json.load(open(0)))
    print('ACCEPT')
