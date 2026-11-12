"""Proof translations between the raw template and parameter calculi.

This module is not trusted by either standalone checker. Every translated
result is replayed by its target checker in the supplied context and scope.
"""
import copy
import raw_template_control as control
import raw_parameter as alias


def rename(a, scope):
    if type(a) is int:
        return a - 1 if a < -scope else a
    return [rename(b, scope) for b in a]


def weaken(proof, scope, length):
    """Insert one fresh parameter and append one clause to the old context."""
    tag, *args = proof
    if tag == 'c':
        return [tag] + [rename(a, scope) for a in args]
    if tag == 'x':
        return [tag] + [weaken(p, scope, length) for p in args]
    if tag == 'u':
        i, target, p = args
        return [tag, i + (i >= length), rename(target, scope),
                weaken(p, scope, length)]
    goal, data, branch = args
    data = weaken(data, scope, length) if tag == 'e' else rename(data, scope)
    return [tag, rename(goal, scope), data, weaken(branch, scope, length)]


def refl(t):
    computation = ['c', 0, t, 1]
    return ['x', computation, computation]


def sym(p, context, scope):
    a, b = alias.derive(p, context, scope)
    return ['x', refl(a), p]


def trans(p, q, context, scope):
    a, b = alias.derive(p, context, scope)
    c, d = alias.derive(q, context, scope)
    if b != c:
        raise ValueError('noncomposable equations')
    return ['x', q, sym(p, context, scope)]


def forward(proof, context=(), scope=0):
    context = list(context)
    tag, *args = proof
    expected = control.derive(proof, context, scope)
    if tag == 'c':
        result = copy.deepcopy(proof)
    elif tag == 'u':
        i, target, p = args
        result = [tag, i, target, forward(p, context, scope)]
    elif tag in ('e', 'i'):
        goal, data, branch = args
        fresh = -scope - 1
        if tag == 'e':
            paired = control.derive(data, context, scope)
            body = control.opening(paired[0], fresh, 2)
            clause = (control.opening(body, 0), body)
            data = forward(data, context, scope)
        else:
            body = control.opening(goal[0], data, 2)
            eta = fresh if len(goal[0]) == 2 and data == 0 else 0
            clause = ([0, 0], control.opening(body, eta))
        result = [tag, goal, data, forward(branch, context + [clause], scope + 1)]
    else:
        template, major, minor = args
        p = forward(major, context, scope)
        q = forward(minor, context, scope)
        s, t = alias.derive(p, context, scope)
        # y is index 1, b is index 2, and the iterator state adds one.
        paired = [[[1, s, 3], s]]
        alias_exists = ['i', paired, s, ['c', [0, -scope - 1], s, s]]
        b = -scope - 1
        body = alias.opening(paired[0], b, 2)
        clause = (alias.opening(body, 0), body)
        local = context + [clause]
        p = weaken(p, scope, len(context))
        q = weaken(q, scope, len(context))
        base = ['c', 0, s, b]
        used = ['u', len(context), [0, 0], base]
        computed = ['c', [0, 0], s, b]
        e = ['x', used, computed]  # b = s
        e_t = trans(e, p, local, scope + 1)       # b = t
        k = alias.opening(template, b)
        k_s = ['x', e, refl(k)]
        k_t = ['x', e_t, refl(k)]
        h_s_t = ['x', k_t, k_s]
        branch = ['x', h_s_t, q]
        result = ['e', expected, alias_exists, branch]
    if alias.derive(result, context, scope) != expected:
        raise RuntimeError('forward translation changed the conclusion')
    return result


def abstract(a, source, depth=0):
    """Make a one-hole-variable template from all occurrences of source."""
    if a == source:
        return depth + 1
    if type(a) is int:
        return a
    if len(a) == 2:
        return [0, abstract(a[1], source, depth)]
    return [abstract(t, source, depth + (i == 2)) for i, t in enumerate(a)]


def backward(proof, context=(), scope=0):
    context = list(context)
    tag, *args = proof
    expected = alias.derive(proof, context, scope)
    if tag == 'c':
        result = copy.deepcopy(proof)
    elif tag == 'u':
        i, target, p = args
        result = [tag, i, target, backward(p, context, scope)]
    elif tag in ('e', 'i'):
        goal, data, branch = args
        fresh = -scope - 1
        if tag == 'e':
            paired = alias.derive(data, context, scope)
            body = alias.opening(paired[0], fresh, 2)
            clause = (alias.opening(body, 0), body)
            data = backward(data, context, scope)
        else:
            body = alias.opening(goal[0], data, 2)
            eta = fresh if len(goal[0]) == 2 and data == 0 else 0
            clause = ([0, 0], alias.opening(body, eta))
        result = [tag, goal, data, backward(branch, context + [clause], scope + 1)]
    else:
        major, minor = args
        s, t = alias.derive(major, context, scope)
        u, r = alias.derive(minor, context, scope)
        template = (1 if u == s else abstract(u, s)
                    if type(s) is int and s < 0 else u)
        result = ['x', template, backward(major, context, scope),
                  backward(minor, context, scope)]
    if control.derive(result, context, scope) != expected:
        raise RuntimeError('backward translation changed the conclusion')
    return result


def translate(certificate, to_alias=True):
    source, target = (control, alias) if to_alias else (alias, control)
    source.verify(certificate)
    result = {'goal': certificate['goal'],
              'proof': (forward if to_alias else backward)(certificate['proof'])}
    target.verify(result)
    return result
