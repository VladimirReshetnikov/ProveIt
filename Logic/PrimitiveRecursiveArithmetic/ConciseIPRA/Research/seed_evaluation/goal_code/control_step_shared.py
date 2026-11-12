"""Step control with the same shared syntax/substitution traversal.

Terms are 0, positive bound indices, negative fresh levels, [0,t] (S),
and [n,a,h] (I). Formulas are [s,t] or [B] (D); terms are zero-normal.
The traversal sorts are -1 (root may have either sort), 0 (term), 1 (formula).
D binds two variables in its only child; I binds one in its third child.
Syntax validation requires the traversal result to equal the input, thereby
rejecting every stored zero-counter iterator. Opening uses the same traversal
to contract a zero counter newly exposed by substitution. Replacements have
no free positive indices. A validated reflexive goal ignores proof payload.
"""
import json
import sys


def require(condition):
    if not condition:
        raise ValueError('invalid certificate')


def walk(a, f, depth=0, sort=-1):
    if type(a) is int:
        require(sort != 1)
        return f(a, depth)
    require(type(a) is list)
    size = len(a)
    require(size in (1, 2, 3) and (sort < 0 or
            (size < 3 if sort else size > 1 and (size == 3 or a[0] == 0))))
    result = [walk(t, f, depth + (2 if size == 1 else int(size == 3 and i == 2)), size == 1)
              for i, t in enumerate(a)]
    return result[1] if size == 3 and result[0] == 0 else result


def syntax(a, scope, sort=0):
    def variable(i, depth):
        require(-scope <= i <= depth)
        return i
    require(walk(a, variable, sort=sort) == a)


def opening(a, value, depth=0):
    return walk(a, lambda i, d: value if i == d + 1 else i - (i > d + 1), depth)


def prove(a, p, g, n):
    syntax(a, n, 1)
    if len(a) == 2 and a[0] == a[1]:
        return
    match p:
        case ['v', c, b, h, t, major, minor]:
            require(len(a) == 2 and a[1] == opening(h, t))
            prove([b if c == 0 else [c, b, h], t], major, g, n)
            prove([[[0, c], b, h], a[0]], minor, g, n)
        case ['u', index, t, premise]:
            require(type(index) is int and 0 <= index < len(g))
            syntax(t, n)
            antecedent, body = g[index]
            require(a == opening(body, t))
            prove(antecedent, premise, g, n)
        case ['e', body, major, branch]:
            prove([body], major, g, n)
            body = opening(body, -n - 1, 1)
            prove(a, branch, g + [(opening(body, 0), body)], n + 1)
        case ['i', t, branch]:
            require(len(a) == 1)
            syntax(t, n)
            body = opening(a[0], t, 1)
            hypothesis = opening(body, -n - 1 if len(a[0]) == 2 and t == 0 else 0)
            prove(opening(body, [0, -n - 1]), branch, g + [([0, 0], hypothesis)], n + 1)
        case _:
            raise ValueError('invalid proof')


def check(c):
    require(type(c) is dict and set(c) == {'goal', 'proof'})
    prove(c['goal'], c['proof'], [], 0)


if __name__ == '__main__':
    try:
        check(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
