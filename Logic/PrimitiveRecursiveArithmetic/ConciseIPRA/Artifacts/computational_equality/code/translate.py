"""Untrusted proof translations. The standalone checkers never import this file.

The input/output sequents retain precisely the same raw terms and formulas.
Both directions validate their input and their generated output.
"""
import copy
import checker as new
import control as old

Z = ['z']
V = ['v', 0]


def eq(s, t):
    return ['=', s, t]


def iterator(c, a, h):
    return ['i', c, a, h]


def ev(p, q):
    return ['ev', p, q]


def refl(a):
    return ['refl', a]


def new_sym(p, g, n):
    _, s, _ = new.infer(p, g, n)
    return ev(refl(s), p)


def new_trans(p, q, g, n):
    return ev(q, new_sym(p, g, n))


def new_zero(a, h):
    return ev(refl(a), refl(iterator(Z, a, h)))


def new_beta(a, h):
    return ev(new_zero(a, h), refl(iterator(['s', Z], a, h)))


def new_congruence(p, h, g, n):
    _, s, _ = new.infer(p, g, n)
    predecessor_value = ev(p, refl(iterator(Z, s, h)))
    return ev(predecessor_value, new_beta(s, h))


def new_successor(c, a, h, g, n):
    return ev(refl(iterator(c, a, h)), refl(iterator(['s', c], a, h)))


def old_refl(a):
    p = ['zero', a, Z]
    return ['tr', V, p, p]


def old_sym(p, g, n):
    _, s, _ = old.infer(p, g, n)
    return ['tr', V, old_refl(s), p]


def old_trans(p, q, g, n):
    return ['tr', V, q, old_sym(p, g, n)]


def old_congruence(p, h, g, n):
    _, s, _ = old.infer(p, g, n)
    return ['tr', h, p, old_refl(old.sub(h, s))]


def old_beta(a, h, g, n):
    return old_trans(['succ', Z, a, h],
                     old_congruence(['zero', a, h], h, g, n), g, n)


def lift_protected(a, protected):
    """Insert one ambient variable, leaving protected external binders fixed."""
    return old.walk(a, lambda i, d: ['v', i + (i >= d + protected)])


def old_eval(p, q, g, n):
    _, s, t = old.infer(p, g, n)
    _, b, _ = old.infer(q, g, n)
    if b == s:
        return ['tr', V, p, q]
    _, c, a, h = b
    if c == Z:
        if a != s:
            raise ValueError('Mismatched initializer')
        computation = ['zero', a, h]
        combined = old_trans(computation, p, g, n)
    elif c[0] == 's':
        if iterator(c[1], a, h) != s:
            raise ValueError('Mismatched predecessor value')
        computation = ['succ', c[1], a, h]
        combined = old_trans(computation, old_congruence(p, h, g, n), g, n)
    else:
        raise ValueError('Blocked iterator counter')
    return ['tr', V, combined, q]


def translate_proof(p, g, n, to_new):
    source = old if to_new else new
    tag = p[0]
    go = lambda proof, context=g, scope=n: translate_proof(proof, context, scope, to_new)
    if tag == 'hyp':
        return copy.deepcopy(p)
    if to_new and tag == 'zero':
        return new_zero(p[1], p[2])
    if to_new and tag == 'succ':
        return new_successor(*p[1:], g, n)
    if to_new and tag == 'tr':
        _, h, major, minor = p
        return ev(new_congruence(go(major), h, g, n), go(minor))
    if not to_new and tag == 'refl':
        return old_refl(p[1])
    if not to_new and tag == 'ev':
        return old_eval(go(p[1]), go(p[2]), g, n)
    if tag == 'qe':
        return [tag, copy.deepcopy(p[1]), go(p[2]), go(p[3])]
    if tag == 'de':
        _, goal, major, branch = p
        paired = source.infer(major, g, n)
        extended = [['q', paired[1]]] + [source.shift(x) for x in g]
        return [tag, copy.deepcopy(goal), go(major), go(branch, extended, n + 1)]
    if tag == 'di':
        _, b, t, branch = p
        a = source.sub(['q', b], t)[1]
        hypothesis = a if a[0] == '=' and t == Z else source.shift(source.sub(a, Z))
        extended = [hypothesis] + [source.shift(x) for x in g]
        return [tag, copy.deepcopy(b), copy.deepcopy(t), go(branch, extended, n + 1)]
    raise ValueError('Unknown proof rule')


def certificate(c, to_new=True):
    source, target = (old, new) if to_new else (new, old)
    source.check(c)
    result = copy.deepcopy(c)
    result['proof'] = translate_proof(c['proof'], c['context'], c['variables'], to_new)
    target.check(result)
    return result


def node_count(p):
    tag = p[0]
    if tag in ('hyp', 'refl', 'zero', 'succ'):
        return 1
    if tag == 'ev':
        return 1 + node_count(p[1]) + node_count(p[2])
    if tag in ('tr', 'qe', 'de'):
        return 1 + node_count(p[2]) + node_count(p[3])
    if tag == 'di':
        return 1 + node_count(p[3])
    raise ValueError('Unknown proof rule')


if __name__ == '__main__':
    import argparse
    import json
    import sys
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('direction', choices=['old-to-new', 'new-to-old'])
    args = parser.parse_args()
    print(json.dumps(certificate(json.load(sys.stdin), args.direction == 'old-to-new')))
