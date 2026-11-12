"""Finite proof translations between the two raw clausal calculi.

This module is an untrusted certificate producer. The independent complete
checkers validate its inputs and outputs. All end formulas remain identical.
"""
import clausal_eval as new
import matched_control as old


def old_refl(a):
    computation = ['z', a, 0]
    return ['x', 1, computation, computation]


def old_sym(proof, context, scope):
    s, t = old.derive(proof, context, scope)
    return ['x', 1, old_refl(s), proof]


def old_trans(first, second, context, scope):
    return ['x', 1, second, old_sym(first, context, scope)]


def eval_congruence(template, proof, s):
    a = [0, s, template]
    b = [new.successor(0), s, template]
    zero = ['v', ['r', s], ['r', a]]
    first = ['v', zero, ['r', b]]
    second = ['v', proof, ['r', a]]
    return ['v', second, first]


def translate_tree(proof, context, scope, to_new):
    source = old if to_new else new
    source.derive(proof, context, scope)
    tag = proof[0]
    if tag == 'u':
        return ['u', proof[1], proof[2],
                translate_tree(proof[3], context, scope, to_new)]
    if tag in ('e', 'i'):
        goal, data, branch = proof[1:]
        fresh = -scope - 1
        if tag == 'e':
            paired = source.derive(data, context, scope)
            body = source.opening(paired[0], fresh, 1)
            clause = (source.opening(body, 0), body)
            data = translate_tree(data, context, scope, to_new)
        else:
            body = source.opening(goal[0], data, 1)
            eta = fresh if len(goal[0]) == 2 and data == 0 else 0
            clause = ([0, 0], source.opening(body, eta))
        return [tag, goal, data,
                translate_tree(branch, context + [clause], scope + 1, to_new)]
    if to_new:
        if tag == 'z':
            a, h = proof[1:]
            return ['v', ['r', a], ['r', [0, a, h]]]
        if tag == 's':
            n, a, h = proof[1:]
            return ['v', ['r', [n, a, h]],
                    ['r', [new.successor(n), a, h]]]
        template, major, minor = proof[1:]
        s, t = old.derive(major, context, scope)
        p = translate_tree(major, context, scope, True)
        q = translate_tree(minor, context, scope, True)
        return ['v', eval_congruence(template, p, s), q]
    if tag == 'r':
        return old_refl(proof[1])
    s, t = new.derive(proof[1], context, scope)
    b, r = new.derive(proof[2], context, scope)
    p = translate_tree(proof[1], context, scope, False)
    q = translate_tree(proof[2], context, scope, False)
    if b == s:
        return ['x', 1, p, q]
    n, a, h = b
    if n == 0:
        chain = old_trans(['z', a, h], p, context, scope)
        return ['x', 1, chain, q]
    computation = ['s', n[1], a, h]
    minor = ['x', 1, q, computation]
    return ['x', h, p, minor]


def translate(data, to_new=True):
    source, target = (old, new) if to_new else (new, old)
    source.verify(data)
    result = {'goal': data['goal'],
              'proof': translate_tree(data['proof'], [], 0, to_new)}
    target.verify(result)
    return result
