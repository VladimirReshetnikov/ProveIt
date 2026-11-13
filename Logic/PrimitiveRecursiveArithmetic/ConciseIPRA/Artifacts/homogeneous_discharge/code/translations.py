"""Untrusted proof translations between the matched H4 and H3 checkers.

No translation code is imported by either standalone trusted checker.
"""
import h4_checker as h4


def truth():
    """The compound theorem D_xy(0=0), in any context containing rho at 0."""
    return ['intro', [[0, 0]], 0, ['use', 0, 0, None]]


def weaken(p, cut, depth=0):
    """Insert one fresh numerical variable and one clause at context index cut.

The new numerical variable is outside the depth locally opened variables.
The injected clause is never used. This works for both certificate formats.
"""
    tag = p[0]
    if tag == 'use':
        _, index, t, q = p
        return [tag, index + (index >= cut), h4.lift(t, cutoff=depth),
                None if q is None else weaken(q, cut, depth)]
    if tag == 'intro':
        _, a, t, q = p
        return [tag, h4.lift(a, f=True, cutoff=depth),
                h4.lift(t, cutoff=depth), weaken(q, cut, depth + 1)]
    if tag == 'eval':
        return [tag, weaken(p[1], cut, depth), weaken(p[2], cut, depth)]
    if tag == 'open':
        return [tag, weaken(p[1], cut, depth), weaken(p[2], cut, depth + 1)]
    assert tag == 'discharge'
    return [tag, weaken(p[1], cut, depth),
            weaken(p[2], cut, depth + 1), weaken(p[3], cut, depth + 1)]


def fuse(p, context_length=1):
    tag = p[0]
    if tag == 'use':
        return p[:3] + [None if p[3] is None else fuse(p[3], context_length)]
    if tag == 'intro':
        return p[:3] + [fuse(p[3], context_length + 1)]
    if tag == 'eval':
        return ['discharge', truth(),
                weaken(fuse(p[1], context_length), context_length),
                weaken(fuse(p[2], context_length), context_length)]
    assert tag == 'open'
    major = fuse(p[1], context_length)
    return ['discharge', major, weaken(major, context_length),
            fuse(p[2], context_length + 1)]


def separate(p, n=0, context=None):
    if context is None:
        context = [[1, 1]]
    tag = p[0]
    if tag == 'use':
        return p[:3] + [None if p[3] is None else separate(p[3], n, context)]
    if tag == 'intro':
        _, a, t, q = p
        body = a[0]
        seed = h4.instance(body, [int(h4.diagonal(body)), h4.lift(t)], True, 1)
        extended = h4.branch_context(context, h4.gate(seed))
        return p[:3] + [separate(q, n + 1, extended)]
    assert tag == 'discharge'
    major = separate(p[1], n, context)
    m = h4.check(major, n, context)
    extended = h4.branch_context(context, m[0])
    e = separate(p[2], n + 1, extended)
    f = separate(p[3], n + 1, extended)
    result = h4.check(e, n + 1, extended)
    return ['open', major, f if len(result) == 1 else ['eval', e, f]]


def deep_reflexivity(a, n, context):
    """Explicit proof of D^k(r=r) using omission at rho alone."""
    if len(a) == 2:
        assert a[0] == a[1]
        return ['use', 0, a[0], None]
    b = a[0]
    seed = h4.instance(b, [int(h4.diagonal(b)), 0], True, 1)
    target = h4.instance(b, [[1], 0], True, 1)
    extended = h4.branch_context(context, h4.gate(seed))
    return ['intro', a, 0, deep_reflexivity(target, n + 1, extended)]


def explicit_bases(p, n=0, context=None):
    """Translate H4 to its fixed-seed version, supplying every other base."""
    if context is None:
        context = [[1, 1]]
    tag = p[0]
    if tag == 'use':
        _, index, t, q = p
        if q is None and index != 0:
            base = h4.instance(context[index], [0], True)
            q = deep_reflexivity(base, n, context)
        elif q is not None:
            q = explicit_bases(q, n, context)
        return [tag, index, t, q]
    if tag == 'intro':
        _, a, t, q = p
        b = a[0]
        seed = h4.instance(b, [int(h4.diagonal(b)), h4.lift(t)], True, 1)
        extended = h4.branch_context(context, h4.gate(seed))
        return p[:3] + [explicit_bases(q, n + 1, extended)]
    if tag == 'eval':
        return [tag, explicit_bases(p[1], n, context),
                explicit_bases(p[2], n, context)]
    assert tag == 'open'
    major = explicit_bases(p[1], n, context)
    m = h4.check(major, n, context)
    extended = h4.branch_context(context, m[0])
    return [tag, major, explicit_bases(p[2], n + 1, extended)]
