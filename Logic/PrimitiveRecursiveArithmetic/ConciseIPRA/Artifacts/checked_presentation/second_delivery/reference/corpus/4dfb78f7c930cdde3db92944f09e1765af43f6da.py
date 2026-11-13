"""Untrusted proof translators between the eight-rule and diagonal seven-rule cores.

The target standalone checker validates every output.  The routines below are
finite syntax transformations; no source proof or claimed conclusion is trusted
by a checker.  Run as ``python3 translate.py native < certificate.json``.
"""

import json
import sys


Z = ['z']


def V(i):
    return ['v', i]


def S(t):
    return ['s', t]


def Eq(s, t):
    return ['=', s, t]


def Q(a):
    return ['q', a]


def I(c, a, h):
    return ['i', c, a, h]


def hyp(i):
    return ['hyp', i]


def map_ast(a, sigma, protected=0):
    """Simultaneously substitute ambient variables, preserving local binders."""
    tag = a[0]
    if tag == 'v':
        i = a[1]
        return V(i) if i < protected else shift(sigma(i - protected), protected)
    increments = {'i': (0, 0, 1), 'q': (1,), 'd': (2,)}.get(tag)
    return [tag] + [map_ast(b, sigma, protected + (increments[j] if increments else 0))
                    for j, b in enumerate(a[1:])]


def shift(a, amount=1, cutoff=0):
    # An independent renamer avoids a recursive call to map_ast/shift on variables.
    if a[0] == 'v':
        return V(a[1] + amount if a[1] >= cutoff else a[1])
    increments = {'i': (0, 0, 1), 'q': (1,), 'd': (2,)}.get(a[0])
    return [a[0]] + [shift(b, amount, cutoff + (increments[j] if increments else 0))
                     for j, b in enumerate(a[1:])]


def sub(a, t, drop=1):
    return map_ast(a, lambda i: t if i == 0 else V(i - drop))


def map_proof(p, sigma, depth=0):
    """Substitute the variables ambient to a derivation (not eigenvariables)."""
    tag = p[0]
    m = lambda a, k=0: map_ast(a, sigma, depth + k)
    rec = lambda q, k=0: map_proof(q, sigma, depth + k)
    if tag == 'hyp':
        return p[:]
    if tag == 'zero':
        return [tag, m(p[1]), m(p[2], 1)]
    if tag == 'succ':
        return [tag, m(p[1]), m(p[2]), m(p[3], 1)]
    if tag == 'tr':
        return [tag, m(p[1], 1), m(p[2], 1), rec(p[3]), rec(p[4])]
    if tag == 'qe':
        return [tag, m(p[1]), rec(p[2]), rec(p[3])]
    if tag == 'de':
        return [tag, m(p[1]), rec(p[2]), rec(p[3], 1)]
    if tag == 'di':
        return [tag, m(p[1], 2), m(p[2]), rec(p[3], 1)]
    if tag == 'qi':
        return [tag, m(p[1], 1), rec(p[2], 1)]
    raise ValueError('Unknown proof rule: ' + str(tag))


def shift_proof(p, amount=1):
    return map_proof(p, lambda i: V(i + amount))


def weaken(p, amount=1, position=0):
    """Insert assumptions at position in the ambient context."""
    tag = p[0]
    if tag == 'hyp':
        return hyp(p[1] + amount if p[1] >= position else p[1])
    out = p[:]
    if tag == 'tr':
        out[3] = weaken(p[3], amount, position)
        out[4] = weaken(p[4], amount, position)
    elif tag == 'qe':
        out[2] = weaken(p[2], amount, position)
        out[3] = weaken(p[3], amount, position)
    elif tag == 'de':
        out[2] = weaken(p[2], amount, position)
        out[3] = weaken(p[3], amount, position + 1)
    elif tag == 'di':
        out[3] = weaken(p[3], amount, position + 1)
    elif tag == 'qi':
        out[2] = weaken(p[2], amount, position + 1)
    return out


def cut(p, replacement, depth=0):
    """Replace each ambient hypothesis i by replacement(i)."""
    tag = p[0]
    if tag == 'hyp':
        if p[1] < depth:
            return p[:]
        return weaken(shift_proof(replacement(p[1] - depth), depth), depth)
    out = p[:]
    if tag == 'tr':
        out[3] = cut(p[3], replacement, depth)
        out[4] = cut(p[4], replacement, depth)
    elif tag == 'qe':
        out[2] = cut(p[2], replacement, depth)
        out[3] = cut(p[3], replacement, depth)
    elif tag == 'de':
        out[2] = cut(p[2], replacement, depth)
        out[3] = cut(p[3], replacement, depth + 1)
    elif tag == 'di':
        out[3] = cut(p[3], replacement, depth + 1)
    elif tag == 'qi':
        out[2] = cut(p[2], replacement, depth + 1)
    return out


def refl(t):
    p = ['zero', t, V(0)]
    return ['tr', V(0), shift(t), p, p]


def symm(p, s):
    """From p:s=t obtain t=s."""
    return ['tr', V(0), shift(s), p, refl(s)]


def trans(p, q, s):
    """From p:s=t and q:t=u obtain s=u."""
    return ['tr', shift(s), V(0), q, p]


def convert(p, before, after, left, right):
    """Transport Eq(before) to Eq(after) using left:s=s', right:t=t'."""
    p1 = trans(symm(left, before[1]), p, after[1])
    return trans(p1, right, after[1])


def selector(v, a, b):
    return I(v, a, shift(b))


def select_eq(v, a, b):
    return Eq(selector(v, a[1], b[1]), selector(v, a[2], b[2]))


def selector_equations(v, a, b):
    if v == Z:
        return (['zero', a[1], shift(b[1])],
                ['zero', a[2], shift(b[2])])
    if v[0] == 's':
        return (['succ', v[1], a[1], shift(b[1])],
                ['succ', v[1], a[2], shift(b[2])])
    raise ValueError('A selector endpoint must be zero or a successor')


def selector_to(p, v, a, b):
    target = a if v == Z else b
    left, right = selector_equations(v, a, b)
    return convert(p, select_eq(v, a, b), target, left, right)


def selector_from(p, v, a, b):
    source = a if v == Z else b
    selected = select_eq(v, a, b)
    left, right = selector_equations(v, a, b)
    return convert(p, source, selected, symm(left, selected[1]), symm(right, selected[2]))


def guarded(a):
    prefix = ['i', V(0), V(0)]
    return a[0] == '=' and a[1][:3] == a[2][:3] == prefix


def guard_zero(a):
    e = sub(a, Z)
    left = ['zero', e[1][2], e[1][3]]
    right = ['zero', e[2][2], e[2][3]]
    return trans(left, symm(right, e[2]), e[1])


def dummy_matrix(a):
    return shift(a, 1, 1)


def case_di(b, t, p):
    """The old case DI, compiled into the diagonal calculus."""
    a = sub(Q(b), t)[1]
    if guarded(a):
        base = weaken(shift_proof(guard_zero(a)))
        p = cut(p, lambda i: base if i == 0 else hyp(i))
    return ['di', b, t, p]


def case_qi(a, p):
    d = case_di(dummy_matrix(a), Z, p)
    return ['de', Q(a), d, hyp(0)]


def guarded_qi(a, p):
    if not guarded(a):
        raise ValueError('Expected a diagonal guard')
    d = ['di', dummy_matrix(a), Z, p]
    return ['de', Q(a), d, hyp(0)]


def implication(a, b):
    return Q(select_eq(V(0), shift(a), shift(b)))


def imp_intro(a, b, p):
    """From [a]+Gamma |- b derive Gamma |- implication(a,b)."""
    sa, sb = shift(a), shift(b)
    local_a = selector_to(hyp(0), Z, sa, sb)
    body = cut(shift_proof(p), lambda i: local_a if i == 0 else hyp(i))
    target = selector_from(body, S(V(0)), sa, sb)
    return case_qi(select_eq(V(0), sa, sb), target)


def imp_elim(a, b, p, q):
    base = selector_from(q, Z, a, b)
    selected = ['qe', S(Z), p, base]
    return selector_to(selected, S(Z), a, b)


def gate(e):
    """The diagonal guard H_y E(y), with y represented by index zero."""
    return Eq(I(V(0), V(0), shift(e[1])), I(V(0), V(0), shift(e[2])))


def gate_equations(g, t):
    if t[0] != 's':
        raise ValueError('Gate removal requires a successor')
    a = sub(g, t)
    return (['succ', t[1], a[1][2], a[1][3]],
            ['succ', t[1], a[2][2], a[2][3]])


def gate_to(p, e, g, t):
    left, right = gate_equations(g, t)
    return convert(p, sub(g, t), sub(e, t), left, right)


def gate_from(p, e, g, t):
    left, right = gate_equations(g, t)
    a = sub(g, t)
    return convert(p, sub(e, t), a, symm(left, a[1]), symm(right, a[2]))


def compile_qi(e, step):
    """Compile arbitrary equation progress, without a context-dependent case split.

    step has context [E(y)] + shift(Gamma).  Each case proof below first
    discharges its local gate assumption using an equation-implication macro.
    """
    g = gate(e)
    e0, g0 = sub(e, Z), sub(g, Z)
    es = sub(e, S(V(0)), 0)
    phi = implication(g, es)

    # Work over Delta = [E(0)] + Gamma.  The zero branch of Phi has a
    # temporarily retained G(0), which is discharged by imp_intro.
    step0 = map_proof(step, lambda i: Z if i == 0 else V(i - 1))
    phi0 = imp_intro(g0, sub(e, S(Z)), weaken(step0))

    # Successor branch: [G(Sw), E(0), Gamma] |- E(SSw).
    # Substitution keeps w in the new ambient scope and does not drop it.
    steps = map_proof(step, lambda i: S(V(0)) if i == 0 else V(i))
    steps = weaken(steps, position=1)
    lifted_e, lifted_g = shift(e, 1, 1), shift(g, 1, 1)
    gs = sub(lifted_g, S(V(0)))
    ess = sub(lifted_e, S(S(V(0))))
    extract = gate_to(hyp(0), lifted_e, lifted_g, S(V(0)))
    steps = cut(steps, lambda i: extract if i == 0 else hyp(i))
    phis = imp_intro(gs, ess, steps)

    # Cases on Phi in a context independent of its case variable.
    qphi = case_qi(phi, weaken(phis))
    phi_y = ['qe', V(0), shift_proof(qphi), shift_proof(phi0)]
    e_s = imp_elim(g, es, weaken(phi_y), hyp(0))
    g_s = gate_from(e_s, lifted_e, lifted_g, S(V(0)))
    qg = guarded_qi(g, g_s)

    # Under the base E(0), obtain all successor E's from the guard closure.
    g_successor = ['qe', S(V(0)), shift_proof(qg), shift_proof(guard_zero(g))]
    e_successor = gate_to(g_successor, lifted_e, lifted_g, S(V(0)))
    return case_qi(e, e_successor)


def translate_proof(p, source='native'):
    tag = p[0]
    out = p[:]
    if tag == 'tr':
        out[3] = translate_proof(p[3], source)
        out[4] = translate_proof(p[4], source)
    elif tag == 'qe':
        out[2] = translate_proof(p[2], source)
        out[3] = translate_proof(p[3], source)
    elif tag == 'de':
        out[2] = translate_proof(p[2], source)
        out[3] = translate_proof(p[3], source)
    elif tag == 'di':
        body = translate_proof(p[3], source)
        if source == 'native':
            return case_di(p[1], p[2], body)
        a = sub(Q(p[1]), p[2])[1]
        if guarded(a):
            closure = ['qi', a, body]
            body = ['qe', S(V(0)), weaken(shift_proof(closure)), hyp(0)]
        return ['di', p[1], p[2], body]
    elif tag == 'qi':
        if source != 'native':
            raise ValueError('qi is not a rule of the diagonal calculus')
        return compile_qi(p[1], translate_proof(p[2], source))
    elif tag not in ('hyp', 'zero', 'succ'):
        raise ValueError('Unknown proof rule: ' + str(tag))
    return out


def translate_certificate(c, source='native'):
    if source not in ('native', 'diagonal'):
        raise ValueError('source must be native or diagonal')
    return dict(c, proof=translate_proof(c['proof'], source))


def main():
    if len(sys.argv) != 2 or sys.argv[1] not in ('native', 'diagonal'):
        raise SystemExit('usage: translate.py native|diagonal < input.json > output.json')
    c = json.load(sys.stdin)
    json.dump(translate_certificate(c, sys.argv[1]), sys.stdout, separators=(',', ':'))
    sys.stdout.write('\n')


if __name__ == '__main__':
    main()

