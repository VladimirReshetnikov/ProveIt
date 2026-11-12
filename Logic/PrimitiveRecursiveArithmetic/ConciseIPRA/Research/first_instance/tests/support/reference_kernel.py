"""Independent replay of the arity-coded witness-substitution calculus.

This module does not import the proposed checker.  Raw syntax checking,
capture-avoiding substitution and normalization are separately implemented.
It also replays the matched ordinary-elimination/term-transport control.
"""
import json
import sys


class Invalid(ValueError):
    pass


def ensure(ok):
    if not ok:
        raise Invalid('invalid certificate')


def raw_term(a, scope, depth=0):
    if type(a) is int:
        ensure(-scope <= a <= depth)
        return
    ensure(type(a) is list)
    if len(a) == 2:
        ensure(type(a[0]) is int and a[0] == 0)
        raw_term(a[1], scope, depth)
    elif len(a) == 3:
        raw_term(a[0], scope, depth)
        raw_term(a[1], scope, depth)
        raw_term(a[2], scope, depth + 1)
    else:
        raise Invalid('term arity')


def raw_formula(a, scope, depth=0):
    ensure(type(a) is list)
    if len(a) == 2:
        raw_term(a[0], scope, depth)
        raw_term(a[1], scope, depth)
    elif len(a) == 1:
        raw_formula(a[0], scope, depth + 2)
    else:
        raise Invalid('formula arity')


def map_syntax(a, integer, depth=0):
    if type(a) is int:
        return integer(a, depth)
    if len(a) == 1:
        return [map_syntax(a[0], integer, depth + 2)]
    if len(a) == 3:
        return [map_syntax(a[0], integer, depth),
                map_syntax(a[1], integer, depth),
                map_syntax(a[2], integer, depth + 1)]
    return [map_syntax(a[0], integer, depth),
            map_syntax(a[1], integer, depth)]


def lift(a, amount, depth=0):
    return map_syntax(a, lambda i, d: i + amount if i > d else i, depth)


def raw_open(a, t, depth=0):
    def variable(i, d):
        if i == d + 1:
            return lift(t, d)
        return i - 1 if i > d + 1 else i
    return map_syntax(a, variable, depth)


def normal(a):
    if type(a) is int:
        return a
    children = [normal(c) for c in a]
    if len(children) != 3:
        return children
    c, seed, body = children
    if c == 0:
        return seed
    if type(c) is list and len(c) == 2 and c[0] == 0:
        prior = normal([c[1], seed, body])
        return normal(raw_open(body, prior))
    return children


def opening(a, t, depth=0):
    return normal(raw_open(a, t, depth))


def replace_parameter(a, parameter, target):
    # A negative free level never shifts under an object-language binder.
    # The inserted target is not revisited.
    return normal(map_syntax(a, lambda i, d: target if i == parameter else i))


def checked_term(a, scope, depth=0):
    raw_term(a, scope, depth)
    ensure(normal(a) == a)


def checked_formula(a, scope, depth=0):
    raw_formula(a, scope, depth)
    ensure(normal(a) == a)


def derive(p, context, scope, control=False):
    ensure(type(p) is list and p and type(p[0]) is str)
    tag = p[0]
    if tag == 'r' and len(p) == 2:
        checked_term(p[1], scope)
        return [p[1], p[1]]
    if tag == 'u' and len(p) == 4:
        index, target, premise = p[1:]
        ensure(type(index) is int and 0 <= index < len(context))
        checked_term(target, scope)
        antecedent, body = context[index]
        ensure(derive(premise, context, scope, control) == antecedent)
        return opening(body, target)
    if tag == 'i' and len(p) == 4:
        goal, witness, branch = p[1:]
        checked_formula(goal, scope)
        ensure(len(goal) == 1)
        checked_term(witness, scope)
        body = opening(goal[0], witness, 1)
        fresh = -scope - 1
        eta = fresh if len(body) == 2 and witness == 0 else 0
        assumption = opening(body, eta)
        expected = opening(body, [0, fresh])
        got = derive(branch, context + [([0, 0], assumption)], scope + 1, control)
        ensure(got == expected)
        return goal
    if tag == 'e' and len(p) == 4:
        goal, major = p[1:3]
        checked_formula(goal, scope)
        paired = derive(major, context, scope, control)
        ensure(len(paired) == 1)
        fresh = -scope - 1
        body = opening(paired[0], fresh, 1)
        extended = context + [(opening(body, 0), body)]
        if control:
            ensure(derive(p[3], extended, scope + 1, True) == goal)
        else:
            base = opening(body, 0)
            row = opening(body, [0, 0])
            target = row[1] if base == [0, 0] and len(row) == 2 and row[0] == fresh else fresh
            branch = derive(p[3], extended, scope + 1, False)
            exported = replace_parameter(branch, fresh, target)
            ensure(exported == goal)
        return goal
    if control and tag == 't' and len(p) == 4:
        template, major, minor = p[1:]
        checked_term(template, scope, 1)
        equality = derive(major, context, scope, True)
        premise = derive(minor, context, scope, True)
        ensure(len(equality) == 2 and len(premise) == 2)
        source, target = equality
        ensure(opening(template, source) == premise[0])
        return [premise[1], opening(template, target)]
    raise Invalid('proof rule')


def check(data, control=False):
    ensure(type(data) is dict and set(data) == {'goal', 'proof'})
    checked_formula(data['goal'], 0)
    ensure(derive(data['proof'], [], 0, control) == data['goal'])
    return True


if __name__ == '__main__':
    try:
        check(json.load(sys.stdin), '--control' in sys.argv)
    except Exception:
        print('REJECT')
        raise SystemExit(1)
    print('ACCEPT')
