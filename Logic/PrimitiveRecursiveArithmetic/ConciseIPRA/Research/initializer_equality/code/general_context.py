"""General one-context ordinary transport.
Strict six-rule zero-canonical scalar arithmetic; ordinary Q elimination.
The entire command-line checker is contained in this one module.
"""
import json
import sys


def fail():
    raise ValueError('invalid certificate')


def rec(n, a, h):
    return a if n == 0 else [n, a, h]


def successor(a):
    return [a]


def term(t, n):
    if type(t) is int:
        return 0 <= t <= n
    if type(t) is not list:
        return False
    if len(t) == 1:
        return term(t[0], n)
    return (len(t) == 3 and t[0] != 0 and term(t[0], n) and term(t[1], n)
            and term(t[2], n + 1))


def formula(a, n):
    if type(a) is not list or not a:
        return False
    if a[0] == '=':
        return len(a) == 3 and term(a[1], n) and term(a[2], n)
    return (len(a) == 2 and a[0] in ('Q', 'D')
            and formula(a[1], n + (1 if a[0] == 'Q' else 2)))


def action(t, f, depth=0):
    if type(t) is int:
        return t if t <= depth else f(t - depth, depth)
    if type(t[0]) is str:
        extra = 0 if t[0] == '=' else 1 if t[0] == 'Q' else 2
        return [t[0]] + [action(a, f, depth + extra) for a in t[1:]]
    if len(t) == 1:
        return [action(t[0], f, depth)]
    return rec(action(t[0], f, depth), action(t[1], f, depth),
               action(t[2], f, depth + 1))


def shift(t, amount=1, depth=0):
    return action(t, lambda i, d: i + d + amount, depth)


def subst(t, images, depth=0):
    return action(t, lambda i, d: shift(images[i - 1], d)
                  if i <= len(images) else i + d - len(images), depth)


def derive(proof, context, scope):
    if type(proof) is not list or not proof or type(proof[0]) is not str:
        fail()
    tag = proof[0]
    if tag == 'h' and len(proof) == 2:
        index = proof[1]
        if type(index) is int and 0 <= index < len(context):
            return context[index]
        fail()
    if tag == 'r' and len(proof) == 4:
        n, a, h = proof[1:]
        if not (term(n, scope) and term(a, scope) and term(h, scope + 1)):
            fail()
        return ['=', rec(successor(n), a, h),
                subst(h, [rec(n, a, h)])]
    if tag == 'x' and len(proof) == 4:
        template, major, minor = proof[1:]
        if not term(template, scope + 1):
            fail()
        _, source, target = derive(major, context, scope)
        _, left, right = derive(minor, context, scope)
        if left != subst(template, [source]):
            fail()
        return ['=', subst(template, [target]), right]
    if tag == 'q' and len(proof) == 4:
        witness, major, base = proof[1:]
        if not term(witness, scope):
            fail()
        closure = derive(major, context, scope)
        if closure[0] != 'Q':
            fail()
        if derive(base, context, scope) != subst(closure[1], [0]):
            fail()
        return subst(closure[1], [witness])
    if tag == 'e' and len(proof) == 4:
        goal, major, branch = proof[1:]
        if not formula(goal, scope):
            fail()
        paired = derive(major, context, scope)
        if paired[0] != 'D':
            fail()
        extended = [shift(a) for a in context] + [['Q', paired[1]]]
        if derive(branch, extended, scope + 1) != shift(goal):
            fail()
        return goal
    if tag == 'i' and len(proof) == 4:
        goal, witness, branch = proof[1:]
        if not formula(goal, scope) or goal[0] != 'D' or not term(witness, scope):
            fail()
        body = shift(goal[1], 1, 2)
        lifted_witness = shift(witness)
        eta = 1 if goal[1][0] == '=' and witness == 0 else 0
        hypothesis = subst(body, [eta, lifted_witness])
        target = subst(body, [successor(1), lifted_witness])
        extended = [shift(a) for a in context] + [hypothesis]
        if derive(branch, extended, scope + 1) != target:
            fail()
        return goal
    fail()


def verify(data):
    if type(data) is not dict or set(data) != {'goal', 'proof'}:
        fail()
    if not formula(data['goal'], 0):
        fail()
    if derive(data['proof'], [], 0) != data['goal']:
        fail()
    return True


if __name__ == '__main__':
    try:
        verify(json.load(sys.stdin))
    except Exception:
        print('REJECT')
        sys.exit(1)
    print('ACCEPT')
