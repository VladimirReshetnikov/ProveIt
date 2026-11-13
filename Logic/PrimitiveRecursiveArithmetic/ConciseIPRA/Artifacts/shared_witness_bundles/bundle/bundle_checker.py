"""A transparent reference checker for shared-witness bundles and root conversion.

Certificate: [goal, proof]. Free parameters of the goal are universally closed.
The public goal uses native formulas: every 'd' has exactly one matrix.
Multicomponent and empty bundles are auxiliary proof objects only.
Terms: 0 | positive integer variable | ['s', t] | ['i', n, a, u, h].
Formulas: ['=', s, t] | ['q', y, B] | ['d', x, [[y, B], ...]].
The iterator binds u in h only. The bundle binds x and each local y in B.
All comparisons of terms/formulas respect alpha equivalence.
"""

import json
import sys


class Invalid(ValueError):
    pass


def require(condition):
    if not condition:
        raise Invalid("invalid certificate")


def var(x):
    return type(x) is int and x > 0


def term(t):
    if type(t) is int:
        return t >= 0
    if type(t) is not list or not t:
        return False
    if t[0] == 's' and len(t) == 2:
        return term(t[1])
    if t[0] == 'i' and len(t) == 5:
        return term(t[1]) and term(t[2]) and var(t[3]) and term(t[4])
    return False


def formula(a):
    if type(a) is not list or not a:
        return False
    if a[0] == '=' and len(a) == 3:
        return term(a[1]) and term(a[2])
    if a[0] == 'q' and len(a) == 3:
        return var(a[1]) and formula(a[2])
    if a[0] == 'd' and len(a) == 3 and var(a[1]) and type(a[2]) is list:
        return all(type(row) is list and len(row) == 2 and var(row[0])
                   and row[0] != a[1] and formula(row[1]) for row in a[2])
    return False


def public_formula(a):
    if a[0] == '=':
        return True
    if a[0] == 'q':
        return public_formula(a[2])
    return len(a[2]) == 1 and public_formula(a[2][0][1])


def tfree(t):
    if type(t) is int:
        return {t} if t else set()
    if t[0] == 's':
        return tfree(t[1])
    _, n, a, u, h = t
    return tfree(n) | tfree(a) | (tfree(h) - {u})


def ffree(a):
    if a[0] == '=':
        return tfree(a[1]) | tfree(a[2])
    if a[0] == 'q':
        return ffree(a[2]) - {a[1]}
    _, x, rows = a
    return set().union(*(ffree(b) - {x, y} for y, b in rows))


def names(a):
    if type(a) is int:
        return {a}
    if type(a) is list:
        return set().union(*(names(b) for b in a))
    return set()


def fresh(*objects):
    return max(set().union({0}, *(names(a) for a in objects))) + 1


def tsub(t, replacements):
    if type(t) is int:
        return replacements.get(t, t) if t else 0
    if t[0] == 's':
        return ['s', tsub(t[1], replacements)]
    _, n, a, u, h = t
    active = {v: r for v, r in replacements.items() if v != u}
    if any(u in tfree(r) for r in active.values()):
        w = fresh(t, list(active), list(active.values()))
        h, u = tsub(h, {u: w}), w
    return ['i', tsub(n, replacements), tsub(a, replacements), u, tsub(h, active)]


def fsub(a, replacements):
    if a[0] == '=':
        return ['=', tsub(a[1], replacements), tsub(a[2], replacements)]
    if a[0] == 'q':
        _, y, b = a
        active = {v: r for v, r in replacements.items() if v != y}
        if any(y in tfree(r) for r in active.values()):
            z = fresh(a, list(active), list(active.values()))
            b, y = fsub(b, {y: z}), z
        return ['q', y, fsub(b, active)]
    _, x, rows = a
    active = {v: r for v, r in replacements.items() if v != x}
    if any(x in tfree(r) for r in active.values()):
        z = fresh(a, list(active), list(active.values()))
        rows = [[y, fsub(b, {x: z})] for y, b in rows]
        x = z
    result = []
    for y, b in rows:
        local = {v: r for v, r in active.items() if v != y}
        if any(y in tfree(r) for r in local.values()):
            z = fresh(a, rows, list(local), list(local.values()), x)
            b, y = fsub(b, {y: z}), z
        result.append([y, fsub(b, local)])
    return ['d', x, result]


def talpha(t, bound=()):
    if type(t) is int:
        return ('b', bound.index(t)) if t in bound else ('f', t)
    if t[0] == 's':
        return ('s', talpha(t[1], bound))
    _, n, a, u, h = t
    return ('i', talpha(n, bound), talpha(a, bound), talpha(h, (u,) + bound))


def falpha(a, bound=()):
    if a[0] == '=':
        return ('=', talpha(a[1], bound), talpha(a[2], bound))
    if a[0] == 'q':
        return ('q', falpha(a[2], (a[1],) + bound))
    _, x, rows = a
    return ('d', tuple(falpha(b, (y, x) + bound) for y, b in rows))


def root(t):
    require(type(t) is list and len(t) == 5 and t[0] == 'i')
    _, n, a, u, h = t
    if n == 0:
        return a
    require(type(n) is list and len(n) == 2 and n[0] == 's')
    return tsub(h, {u: ['i', n[1], a, u, h]})


def scoped_term(t, scope):
    require(term(t) and tfree(t) <= scope)


def scoped_formula(a, scope):
    require(formula(a) and ffree(a) <= scope)


def check(p, scope, context):
    require(type(p) is list and bool(p))
    tag = p[0]
    if tag == 'h' and len(p) == 2:
        require(type(p[1]) is int and 0 <= p[1] < len(context))
        a = context[p[1]]
    elif tag == 'r' and len(p) == 2:
        scoped_term(p[1], scope)
        a = ['=', p[1], p[1]]
    elif tag == 'v' and len(p) == 3:
        e, f = [check(q, scope, context) for q in p[1:]]
        require(e[0] == f[0] == '=' and var(e[1]) and e[1] in scope)
        a = ['=', f[2], tsub(f[1], {e[1]: e[2]})]
    elif tag in ('c', 'e') and len(p) == (3 if tag == 'c' else 4):
        require(type(p[1]) is int and p[1] in (0, 1))
        a = list(check(p[-1], scope, context))
        require(a[0] == '=')
        side = p[1] + 1
        if tag == 'c':
            a[side] = root(a[side])
        else:
            scoped_term(p[2], scope)
            require(talpha(root(p[2])) == talpha(a[side]))
            a[side] = p[2]
    elif tag == 'q' and len(p) == 4:
        major, base = [check(q, scope, context) for q in p[1:3]]
        require(major[0] == 'q')
        scoped_term(p[3], scope)
        _, y, b = major
        require(falpha(base) == falpha(fsub(b, {y: 0})))
        a = fsub(b, {y: p[3]})
    elif tag == 'o' and len(p) == 4:
        major = check(p[1], scope, context)
        b = p[2]
        require(major[0] == 'd' and var(b) and b not in scope)
        _, x, rows = major
        added = [fsub(['q', y, body], {x: b}) for y, body in rows]
        a = check(p[3], scope | {b}, context + added)
        require(b not in ffree(a))
    elif tag == 'd' and len(p) == 4:
        a, t, branches = p[1:]
        scoped_formula(a, scope)
        scoped_term(t, scope)
        require(a[0] == 'd' and type(branches) is list and len(branches) == len(a[2]))
        x = a[1]
        for (y, body), branch in zip(a[2], branches):
            require(type(branch) is list and len(branch) == 3)
            z, mode, subproof = branch
            require(var(z) and z not in scope and mode in ('c', 'p'))
            require(mode == 'c' or body[0] == '=')
            seed = fsub(body, {x: t, y: z if mode == 'p' else 0})
            target = fsub(body, {x: t, y: ['s', z]})
            got = check(subproof, scope | {z}, context + [seed])
            require(falpha(got) == falpha(target))
    else:
        raise Invalid("unknown instruction or wrong arity")
    scoped_formula(a, scope)
    return a


def accepts(document):
    try:
        require(type(document) is list and len(document) == 2)
        goal, proof = document
        require(formula(goal) and public_formula(goal))
        got = check(proof, ffree(goal), [])
        return falpha(got) == falpha(goal)
    except (Invalid, IndexError, KeyError, TypeError, ValueError, RecursionError):
        return False


if __name__ == '__main__':
    try:
        print('ACCEPT' if accepts(json.load(sys.stdin)) else 'REJECT')
    except (OSError, ValueError, RecursionError):
        print('REJECT')
