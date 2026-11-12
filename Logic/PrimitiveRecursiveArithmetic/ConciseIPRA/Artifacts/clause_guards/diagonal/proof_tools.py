"""Untrusted proof producers and a translation into the native control.

This module is not imported by either trusted checker.
"""
import copy
import checker as C
import native_diagonal_control as N


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


def to_native(p, context=(), kinds=(), scope=0):
    """Exact end-formula preservation for every primary proof.

    kinds[i] is 'ordinary' or 'canonical', recording the origin of each
    retained clause. These are the only clause kinds generated from an
    empty context by the public primary verifier. A general context of
    arbitrary clauses needs the formula translation in the paper.
    """
    tag = p[0]
    if tag == 'r':
        return copy.deepcopy(p)
    if tag == 'v':
        return ['v', to_native(p[1], context, kinds, scope),
                to_native(p[2], context, kinds, scope)]
    if tag == 'u':
        _, idx, witness, premise = p
        if kinds[idx] == 'ordinary':
            # Checking the input proof ensures the erased premise proves 0=0.
            return ['h', idx]
        return ['q', witness, ['h', idx],
                to_native(premise, context, kinds, scope)]
    _, goal, data, branch = p
    fresh = -scope - 1
    if tag == 'e':
        dp = to_native(data, context, kinds, scope)
        paired = value(data, context, scope)
        body = C.opening(paired[0], fresh, 1)
        clause = (C.opening(body, 0), body)
        nb = to_native(branch, list(context) + [clause],
                       tuple(kinds) + ('canonical',), scope + 1)
        return ['e', goal, dp, nb]
    if tag == 'i':
        ctx, _ = intro_context(goal, data, list(context), scope)
        nb = to_native(branch, ctx, tuple(kinds) + ('ordinary',), scope + 1)
        return ['i', goal, data, nb]
    raise ValueError('unknown proof instruction')


def translate(certificate):
    C.verify(certificate)
    result = {'goal': copy.deepcopy(certificate['goal']),
              'proof': to_native(certificate['proof'])}
    N.verify(result)
    return result


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
