"""Untrusted proof producers for the mirror clausal checker.

This module is not imported by either trusted checker.
"""
import copy
import checker as C


def S(a):
    return [0, a]


def I(c, a, h):
    return [c, a, h]


def eq(a, b):
    return [a, b]


def refl(a):
    return ['r', a]


def value(p, context=(), scope=0):
    return C.derive(p, list(context), scope)


def zero(a, h):
    return ['v', refl(a), refl(I(0, a, h))]


def successor(c, a, h):
    return ['v', refl(I(c, a, h)), refl(I(S(c), a, h))]


def pivot(p, q, context=(), scope=0):
    s, _ = value(p, context, scope)
    assert value(q, context, scope)[0] == s
    return ['v', p, ['v', q, refl(I(0, s, 1))]]


def sym(p, context=(), scope=0):
    s, _ = value(p, context, scope)
    return pivot(refl(s), p, context, scope)


def trans(p, q, context=(), scope=0):
    assert value(p, context, scope)[1] == value(q, context, scope)[0]
    return pivot(q, sym(p, context, scope), context, scope)


def transport(h, p, q, context=(), scope=0):
    s, _ = value(p, context, scope)
    assert value(q, context, scope)[0] == C.opening(h, s)
    first = trans(zero(s, h), p, context, scope)
    bridge = ['v', zero(s, h), refl(I(S(0), s, h))]
    second = trans(bridge, q, context, scope)
    return ['v', first, second]


def congr(h, p, context=(), scope=0):
    s, _ = value(p, context, scope)
    return transport(h, p, refl(C.opening(h, s)), context, scope)


def ordinary(a):
    """No free positive index occurs in a; an unused new binder needs no edit."""
    return ([0, 0], a)


def use(index, target=0, premise=None):
    return ['u', index, target, refl(0) if premise is None else premise]


def intro_context(goal, witness, context, scope):
    body = C.opening(goal[0], witness, 1)
    fresh = -scope - 1
    eta = fresh if C.diagonal(goal[0]) else 0
    assumption = C.opening(body, eta)
    target = C.opening(body, S(fresh))
    return context + [ordinary(assumption)], target


def substitute(data, images, old_scope, new_scope):
    """Free-parameter substitution plus uniform eigenparameter renaming.

    images maps -1,...,-old_scope to terms valid in new_scope. Positive
    local indices and non-variable metadata are unchanged. Every proper
    branch eigenparameter -(old_scope+j) becomes -(new_scope+j).
    """
    for i in range(1, old_scope + 1):
        assert C.term(images[-i], new_scope)
    if type(data) is int:
        if data >= 0:
            return data
        if data >= -old_scope:
            return copy.deepcopy(images[data])
        return data + old_scope - new_scope
    if type(data) is list:
        return [substitute(x, images, old_scope, new_scope) for x in data]
    if type(data) is tuple:
        return tuple(substitute(x, images, old_scope, new_scope) for x in data)
    return data
