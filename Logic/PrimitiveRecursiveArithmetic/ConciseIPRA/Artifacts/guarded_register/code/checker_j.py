import json
BINDERS = {'=': 0, 'q': 1, 'd': 2, 'j': 1}

def require(condition):
    if not condition:
        raise ValueError('Invalid certificate')

def subst(a, values=(), delta=0, depth=0):
    if type(a) is int:
        if a <= depth:
            return a
        index = a - depth - 1
        if index < len(values):
            return subst(values[index], delta=depth)
        return a - len(values) + delta
    return [a[0]] + [subst(x, values, delta, depth + (BINDERS[a[0]] if i == len(a) - 1 else 0)) for i, x in enumerate(a[1:], 1)]

def term(a, depth):
    if type(a) is int:
        require(0 <= a <= depth)
    else:
        require(type(a) is list and len(a) == 3 and (a[0] == 'j'))
        term(a[1], depth)
        term(a[2], depth + 1)
        body = a[2]
        require(subst(body, (0,), 1) == body or body[2] == 0)

def formula(a, depth):
    require(type(a) is list and a)
    if a[0] == '=':
        require(len(a) == 3)
        term(a[1], depth)
        term(a[2], depth)
    else:
        require(len(a) == 2 and a[0] in ('q', 'd'))
        formula(a[1], depth + BINDERS[a[0]])

def succ(a):
    return ['j', a, 0]

def eq(a, b):
    return ['=', a, b]

def extend(context, assumption):
    return tuple((subst(a, delta=1) for a in context)) + (assumption,)

def prove(p, context=(), depth=0):
    require(type(p) is list and p)
    rule, *args = p
    if rule == 'hyp':
        index, = args
        require(type(index) is int and 0 <= index < len(context))
        return context[index]
    if rule == 'j0':
        body, = args
        value = ['j', 0, body]
        term(value, depth)
        return eq(value, succ(subst(body, (0,))))
    if rule == 'js':
        n, body = args
        value = ['j', n, succ(body)]
        term(value, depth)
        return eq(['j', succ(n), succ(body)], subst(body, (value,)))
    if rule == 'tr':
        template, major, minor = args
        term(template, depth + 1)
        e = prove(major, context, depth)
        f = prove(minor, context, depth)
        require(e[0] == f[0] == '=' and f[1] == subst(template, (e[1],)))
        return eq(f[2], subst(template, (e[2],)))
    if rule == 'qe':
        t, major, minor = args
        term(t, depth)
        q = prove(major, context, depth)
        require(q[0] == 'q')
        require(prove(minor, context, depth) == subst(q[1], (0,)))
        return subst(q[1], (t,))
    if rule == 'de':
        major, branch = args
        d = prove(major, context, depth)
        require(d[0] == 'd')
        f = prove(branch, extend(context, ['q', d[1]]), depth + 1)
        require(subst(f, (0,), 1) == f)
        return subst(f, (0,))
    if rule == 'di':
        body, witness, branch = args
        formula(body, depth + 2)
        term(witness, depth)
        base = subst(body, (0, witness))
        target = subst(body, (succ(1), subst(witness, delta=1)), delta=1)
        require(prove(branch, extend(context, subst(base, delta=1)), depth + 1) == target)
        return ['d', body]
    if rule == 'qi':
        body, branch = args
        formula(body, depth + 1)
        require(body[0] == '=')
        target = subst(body, (succ(1),), delta=1)
        require(prove(branch, extend(context, body), depth + 1) == target)
        return ['q', body]
    raise ValueError('Unknown proof rule')

def main():
    goal, proof = json.load(open(0))
    formula(goal, 0)
    require(prove(proof) == goal)
    print('ACCEPT')
if __name__ == '__main__':
    main()
