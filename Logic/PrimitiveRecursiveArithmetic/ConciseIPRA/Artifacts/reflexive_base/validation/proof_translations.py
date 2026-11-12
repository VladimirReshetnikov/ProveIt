"""Untrusted, constructive translations between two zero-normal calculi.

The standalone kernels do not import this module.  Every delivered result is
checked by the destination kernel.  'seven' has separate case DI and QI;
'six' chooses progress precisely when the normalized zero instance is a
reflexive literal equation.  There is no witness test in six.
"""
from dataclasses import dataclass
from copy import deepcopy
import zero_seven as seven
import reflexive_base as six

Z = ['z']
V = ['v', 0]
SV = ['s', V]


def norm(a):
    return seven.walk(a, lambda i, d: ['v', i])


def eq(s, t):
    return ['=', s, t]


def sel(c, a, b):
    return norm(['i', c, a, seven.shift(b)])


def map_proof(p, at, hyp=lambda i, local: ['hyp', i], local=0):
    """Map outer numerical parameters and hypotheses, protecting binders."""
    tag = p[0]
    if tag == 'hyp':
        return hyp(p[1], local)
    if tag == 'succ':
        return [tag, at(p[1], local), at(p[2], local), at(p[3], local + 1)]
    if tag == 'tr':
        return [tag, at(p[1], local + 1),
                map_proof(p[2], at, hyp, local), map_proof(p[3], at, hyp, local)]
    if tag in ('qe', 'de'):
        return [tag, at(p[1], local), map_proof(p[2], at, hyp, local),
                map_proof(p[3], at, hyp, local + (tag == 'de'))]
    if tag == 'di':
        return [tag, at(p[1], local + 2), at(p[2], local),
                map_proof(p[3], at, hyp, local + 1)]
    if tag == 'qi':
        return [tag, at(p[1], local + 1), map_proof(p[2], at, hyp, local + 1)]
    raise ValueError('Unknown proof node')


def lift_tree(p, amount=1):
    def at(a, protected):
        return seven.walk(a, lambda i, d: ['v', i + amount
                          if i >= d + protected else i])
    return map_proof(p, at)


def weaken_tree(p, amount=1):
    return map_proof(p, lambda a, _: deepcopy(a),
                     lambda i, local: ['hyp', i + amount if i >= local else i])


def cut_tree(p, replacements):
    """Replace each outer hypothesis by a proof, with no numerical substitution."""
    def hyp(i, local):
        if i < local:
            return ['hyp', i]
        return weaken_tree(lift_tree(replacements(i - local), local), local)
    return map_proof(p, lambda a, _: deepcopy(a), hyp)


def substitute_seven_tree(p, sigma):
    """Simultaneous term substitution in the seven-rule calculus only."""
    def at(a, protected):
        return seven.walk(a, lambda i, d: ['v', i] if i < d + protected
                          else seven.shift(sigma[i - d - protected], d + protected))
    return map_proof(p, at)


@dataclass
class D:
    a: list
    p: list

    def lifted(self, amount=1):
        return D(seven.shift(self.a, amount), lift_tree(self.p, amount))

    def weakened(self, amount=1):
        return D(self.a, weaken_tree(self.p, amount))


def hyp(a, i=0):
    return D(a, ['hyp', i])


def comp(c, a, h):
    return D(eq(['i', ['s', c], a, h], seven.sub(h, ['i', c, a, h])),
             ['succ', c, a, h])


def tr(h, e, f):
    assert e.a[0] == f.a[0] == '='
    assert f.a[1] == seven.sub(h, e.a[1]), (f.a, h, e.a)
    return D(eq(f.a[2], seven.sub(h, e.a[2])), ['tr', h, e.p, f.p])


def refl(t):
    e = comp(Z, Z, seven.shift(t))
    return tr(V, e, e)


def sym(e):
    return tr(V, refl(e.a[1]), e)


def trans(e, f):
    assert e.a[2] == f.a[1], (e.a, f.a)
    return tr(V, f, sym(e))


def congr(h, e):
    return tr(h, e, refl(seven.sub(h, e.a[1])))


def between(left, middle, right):
    """left: L=l; middle: l=r; right: R=r; return L=R."""
    return trans(left, trans(middle, sym(right)))


def qe(t, closure, base):
    assert closure.a[0] == 'q'
    assert base.a == seven.sub(closure.a[1], Z), (closure.a, base.a)
    return D(seven.sub(closure.a[1], t), ['qe', t, closure.p, base.p])


def dummy(b):
    return seven.shift(['q', b])[1]


def is_guarded(a):
    b = seven.sub(a, Z)
    return b[0] == '=' and b[1] == b[2]


def di_case(b, t, p):
    """Recover unrestricted case DI inside the guarded six-rule calculus.

    p is supplied in the case-rule context, beginning with B(t,0).
    If that base is reflexive, replace it by its proof and then add the
    progress hypothesis.  This is the branch that repairs substitutions
    which change a false guard into a true guard.
    """
    a = seven.sub(['q', b], t)[1]
    if is_guarded(a):
        base = seven.sub(a, Z)
        replacement = refl(seven.shift(base[1])).p
        p = cut_tree(p, lambda i: replacement if i == 0 else ['hyp', i - 1])
        p = weaken_tree(p)
    return D(['d', b], ['di', b, t, p])


def q_case(b, p):
    """Derived Q introduction by cases; p has the retained base hypothesis."""
    d = di_case(dummy(b), Z, p)
    return D(['q', b], ['de', ['q', b], d.p, ['hyp', 0]])


def q_guard_progress(b, p):
    assert is_guarded(b)
    d = ['di', dummy(b), Z, p]
    return D(['q', b], ['de', ['q', b], d, ['hyp', 0]])


def guarded_equation(e):
    assert e[0] == '='
    return eq(sel(V, Z, e[1]), sel(V, Z, e[2]))


def decoder_closure(s, seed):
    """Q_y (C(y,seed,C(y,0,s(y))) = s(y)).

    Its zero instance is seed=s(0).  Successor computation proves the
    step without assumptions, so q_case may choose either guard branch.
    s is a template with the displayed y at variable zero; seed is outside.
    """
    body = eq(sel(V, seven.shift(seed), sel(V, Z, s)), s)
    ss = seven.sub(s, SV, 0)
    inner = sel(SV, Z, ss)
    outer = comp(V, seven.shift(seed), seven.shift(inner))
    inner_eq = comp(V, Z, seven.shift(ss))
    step = trans(outer, inner_eq)
    assert step.a == seven.sub(body, SV, 0)
    return q_case(body, step.p)


def qi_to_six(e, premise, g, n):
    """Construct guarded proofs of an arbitrary seven-rule QI conclusion.

    premise already belongs to six, in context [E(z)] + shift(g).
    E(0) is retained while H(y)=C(y,0,s(y))=C(y,0,t(y)) is iterated.
    Decoder equalities recover E(z) from H(z), so the input progress
    premise is actually used.  Final Q-by-cases discharges E(0).
    """
    s, t = e[1:]
    base = seven.sub(e, Z)
    seed = base[1]
    h = guarded_equation(e)
    assert seven.sub(h, Z) == eq(Z, Z)

    # hstep context: [H(z), E(0)^+] + g^+.
    left_q = decoder_closure(s, seed).lifted().weakened()
    right_q = decoder_closure(t, seed).lifted().weakened()
    left_base = refl(seven.shift(seed))
    right_base = hyp(seven.shift(base), 1)
    dl = qe(V, left_q, left_base)
    dr = qe(V, right_q, right_base)
    decode_template = sel(['v', 1], seven.shift(seed, 2), V)
    decoded = trans(sym(dl), trans(congr(decode_template, hyp(h)), dr))
    assert decoded.a == e, (decoded.a, e)

    used_step = cut_tree(premise, lambda i: decoded.p if i == 0 else ['hyp', i + 1])
    es = seven.sub(e, SV, 0)
    st = D(es, used_step)
    lc = comp(V, Z, seven.shift(es[1]))
    rc = comp(V, Z, seven.shift(es[2]))
    hs = between(lc, st, rc)
    assert hs.a == seven.sub(h, SV, 0)
    qh = q_guard_progress(h, hs.p)

    # QH is in [E(0)] + g.  Lift its numerical parameters and use target Sz.
    shifted_qh = qh.lifted()
    hs_again = qe(SV, shifted_qh, refl(Z))
    # Its terms are H(Sz) with the original parameters lifted; these match
    # es because e's distinguished variable becomes the fresh outer z.
    left = comp(V, Z, seven.shift(es[1]))
    right = comp(V, Z, seven.shift(es[2]))
    final_step = trans(sym(left), trans(hs_again, right))
    assert final_step.a == es
    return q_case(e, final_step.p)


def to_six(p, g, n):
    tag = p[0]
    if tag in ('hyp', 'succ'):
        return deepcopy(p)
    if tag in ('tr', 'qe'):
        return [tag, p[1], to_six(p[2], g, n), to_six(p[3], g, n)]
    if tag == 'de':
        b = seven.infer(p[2], g, n)
        subg = [['q', b[1]]] + [seven.shift(x) for x in g]
        return [tag, p[1], to_six(p[2], g, n), to_six(p[3], subg, n + 1)]
    if tag == 'di':
        a = seven.sub(['q', p[1]], p[2])[1]
        subg = [seven.shift(seven.sub(a, Z))] + [seven.shift(x) for x in g]
        return di_case(p[1], p[2], to_six(p[3], subg, n + 1)).p
    if tag == 'qi':
        e = p[1]
        subg = [e] + [seven.shift(x) for x in g]
        return qi_to_six(e, to_six(p[2], subg, n + 1), g, n).p
    raise ValueError('Unknown seven-rule proof')


def to_seven(p, g, n):
    tag = p[0]
    if tag in ('hyp', 'succ'):
        return deepcopy(p)
    if tag in ('tr', 'qe'):
        return [tag, p[1], to_seven(p[2], g, n), to_seven(p[3], g, n)]
    if tag == 'de':
        b = six.infer(p[2], g, n)
        subg = [['q', b[1]]] + [seven.shift(x) for x in g]
        return [tag, p[1], to_seven(p[2], g, n), to_seven(p[3], subg, n + 1)]
    if tag == 'di':
        b, t = p[1:3]
        a = seven.sub(['q', b], t)[1]
        base = seven.sub(a, Z)
        local = a if is_guarded(a) else seven.shift(base)
        subg = [local] + [seven.shift(x) for x in g]
        premise = to_seven(p[3], subg, n + 1)
        if not is_guarded(a):
            return [tag, b, t, premise]
        closure = D(['q', a], ['qi', a, premise]).lifted().weakened()
        step = qe(SV, closure, hyp(seven.shift(base)))
        return [tag, b, t, step.p]
    raise ValueError('Unknown guarded proof')


def translate_certificate(c, direction):
    if direction not in ("to_six", "to_seven"):
        raise ValueError("Unknown translation direction")
    source, target, translate = ((seven, six, to_six) if direction == 'to_six'
                                 else (six, seven, to_seven))
    source.check(c)
    result = dict(c, proof=translate(c['proof'], c['context'], c['variables']))
    target.check(result)
    return result


def substitute_guarded_certificate(c, sigma, variables):
    """Admissible substitution, including a false-to-true guard change.

    Translate through seven, where both introductions commute directly
    with substitution, then elaborate back into the guarded calculus.
    """
    old = translate_certificate(c, 'to_seven')
    assert len(sigma) == c['variables']
    for t in sigma:
        seven.term(t, variables)
    def subst(a):
        return seven.walk(a, lambda i, d: ['v', i] if i < d
                          else seven.shift(sigma[i - d], d))
    substituted = dict(variables=variables,
                       context=[subst(a) for a in old['context']],
                       goal=subst(old['goal']),
                       proof=substitute_seven_tree(old['proof'], sigma))
    seven.check(substituted)
    return translate_certificate(substituted, 'to_six')
