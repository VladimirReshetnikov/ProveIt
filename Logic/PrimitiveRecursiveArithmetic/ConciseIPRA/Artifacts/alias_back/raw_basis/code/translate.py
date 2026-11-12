"""Untrusted compilers: template equality -> arbitrary-variable aliases -> newest.

Every completed compiler call is checked by its standalone target module.
"""
import copy
import raw_template_matched as C
import raw_alias_unrestricted as U
import raw_alias as N


def rename_insert(a, scope):
    if type(a) is int:
        return a - 1 if a < -scope else a
    return [rename_insert(b, scope) for b in a]


def weaken(proof, scope, length):
    """Admissible weakening in the arbitrary-parameter calculus only."""
    tag, *args = proof
    if tag == 'c':
        return [tag] + [rename_insert(a, scope) for a in args]
    if tag == 'u':
        j, t, p = args
        return [tag, j + (j >= length), rename_insert(t, scope),
                weaken(p, scope, length) if p is not None else None]
    if tag == 'v':
        F, p, q = args
        return [tag, rename_insert(F, scope), weaken(p, scope, length), weaken(q, scope, length)]
    if tag == 'a':
        t, p = args
        return [tag, rename_insert(t, scope), weaken(p, scope, length)]
    goal, data, branch = args
    data = weaken(data, scope, length) if tag == 'e' else rename_insert(data, scope)
    return [tag, rename_insert(goal, scope), data, weaken(branch, scope, length)]


def hyp(index):
    return ['u', index, 0, None]


def newest_hyp(index):
    return ['u', index, None]


def refl(t, context, scope):
    return ['a', t, hyp(len(context))]


def sym(p, context, scope):
    s, t = U.derive(p, context, scope)
    b = -scope - 1
    local = context + [([], [b, s])]
    equality = ['v', [b, t], hyp(len(context)), weaken(p, scope, len(context))]
    result = ['a', s, ['v', [t, b], equality, refl(t, local, scope + 1)]]
    if U.derive(result, context, scope) != [t, s]:
        raise RuntimeError('symmetry compiler')
    return result


def transport(template, p, q, context, scope):
    s, t = U.derive(p, context, scope)
    lhs, rhs = U.derive(q, context, scope)
    if lhs != U.opening(template, s):
        raise ValueError('bad transport inputs')
    b = -scope - 1
    local = context + [([], [b, t])]
    reverse = sym(p, context, scope)
    b_equals_s = ['v', [b, s], hyp(len(context)), weaken(reverse, scope, len(context))]
    F = [U.opening(template, b), rhs]
    branch = ['v', F, b_equals_s, weaken(q, scope, len(context))]
    forward = ['a', t, branch]
    result = sym(forward, context, scope)
    if U.derive(result, context, scope) != [rhs, U.opening(template, t)]:
        raise RuntimeError('transport compiler')
    return result


def to_unrestricted(proof, context=(), scope=0):
    context = list(context)
    expected = C.derive(proof, context, scope)
    tag, *args = proof
    if tag == 'c':
        out = copy.deepcopy(proof)
    elif tag == 'u':
        j, t, p = args
        out = [tag, j, t, to_unrestricted(p, context, scope) if context[j][0] else None]
    elif tag in ('e', 'i'):
        goal, data, branch = args
        b = -scope - 1
        if tag == 'e':
            paired = C.derive(data, context, scope)
            B = C.opening(paired[0], b, 2)
            clause = (C.opening(B, 0), B)
            data = to_unrestricted(data, context, scope)
        else:
            B = C.opening(goal[0], data, 2)
            eta = b if len(goal[0]) == 2 and data == 0 else 0
            clause = ([], C.opening(B, eta))
        out = [tag, goal, data, to_unrestricted(branch, context + [clause], scope + 1)]
    else:
        template, p, q = args
        out = transport(template, to_unrestricted(p, context, scope),
                        to_unrestricted(q, context, scope), context, scope)
    if U.derive(out, context, scope) != expected:
        raise RuntimeError('template translation changed formula')
    return out


def rename(a, mapping):
    if type(a) is int:
        return mapping[a] if a < 0 else a
    return [rename(b, mapping) for b in a]


def to_newest(proof, source_context=(), source_scope=0,
              target_context=None, target_scope=None, mapping=None, positions=None):
    """Compile directly into each extended target context, never weaken target proofs."""
    source_context = list(source_context)
    target_context = list(source_context) if target_context is None else list(target_context)
    target_scope = source_scope if target_scope is None else target_scope
    mapping = {i: i for i in range(-source_scope, 0)} if mapping is None else dict(mapping)
    positions = list(range(len(source_context))) if positions is None else list(positions)
    expected = rename(U.derive(proof, source_context, source_scope), mapping)
    tag, *args = proof

    def same(p, tg=target_context, ts=target_scope):
        return to_newest(p, source_context, source_scope, tg, ts, mapping, positions)

    if tag == 'c':
        out = [tag] + [rename(a, mapping) for a in args]
    elif tag == 'u':
        j, t, p = args
        tp = rename(t, mapping)
        b = -target_scope - 1
        local = target_context + [([], [b, tp])]
        premise = same(p, local, target_scope + 1) if source_context[j][0] else None
        out = ['a', tp, [tag, positions[j], premise]]
    elif tag == 'v':
        F, p, q = args
        v, t = U.derive(p, source_context, source_scope)
        b = -target_scope - 1
        vp = mapping[v]
        tp = rename(t, mapping)
        local = target_context + [([], [b, vp])]
        eq = ['v', [b, tp], newest_hyp(len(target_context)), same(p, local, target_scope + 1)]
        body = N.opening(rename(F, mapping), b, vp)
        branch = ['v', body, eq, same(q, local, target_scope + 1)]
        out = ['a', vp, branch]
    elif tag == 'a':
        t, p = args
        bs = -source_scope - 1
        bt = -target_scope - 1
        tp = rename(t, mapping)
        sc = source_context + [([], [bs, t])]
        tc = target_context + [([], [bt, tp])]
        out = [tag, tp, to_newest(p, sc, source_scope + 1, tc, target_scope + 1,
                                mapping | {bs: bt}, positions + [len(target_context)])]
    else:
        goal, data, branch = args
        bs = -source_scope - 1
        bt = -target_scope - 1
        if tag == 'e':
            paired = U.derive(data, source_context, source_scope)
            B = U.opening(paired[0], bs, 2)
            source_clause = (U.opening(B, 0), B)
            translated_data = same(data)
        else:
            B = U.opening(goal[0], data, 2)
            eta = bs if len(goal[0]) == 2 and data == 0 else 0
            source_clause = ([], U.opening(B, eta))
            translated_data = rename(data, mapping)
        mapping2 = mapping | {bs: bt}
        target_clause = tuple(rename(a, mapping2) for a in source_clause)
        out = [tag, rename(goal, mapping), translated_data,
               to_newest(branch, source_context + [source_clause], source_scope + 1,
                         target_context + [target_clause], target_scope + 1,
                         mapping2, positions + [len(target_context)])]
    if N.derive(out, target_context, target_scope) != expected:
        raise RuntimeError(('newest translation changed formula', tag))
    return out


def translate(data):
    C.verify(data)
    intermediate = to_unrestricted(data['proof'])
    out = {'goal': data['goal'], 'proof': to_newest(intermediate)}
    N.verify(out)
    return out
