"""Untrusted finite translations between two checked zero-normal calculi."""
import successor_eval as step
import zero_normal_control as control

Z = ['z']
V = ['v', 0]
ONE = ['s', Z]


def ref(a):
    return ['refl', a]


def ev(p, q):
    return ['ev', p, q]


def resolve(p, q, g, n):
    _, s, _ = step.infer(p, g, n)
    return ev(p, ev(q, ref(['i', ONE, s, V])))


def symmetry(p, g, n):
    _, s, _ = step.infer(p, g, n)
    return resolve(ref(s), p, g, n)


def transitivity(p, q, g, n):
    return resolve(q, symmetry(p, g, n), g, n)


def congruence(h, p, q, g, n):
    _, s, _ = step.infer(p, g, n)
    j = ['i', ONE, s, h]
    cp = ev(ref(s), ref(j))
    return ev(p, transitivity(cp, q, g, n))


def control_ref(a):
    cp = ['succ', Z, a, V]
    return ['tr', V, cp, cp]


def control_sym(p, g, n):
    _, s, _ = control.infer(p, g, n)
    return ['tr', V, control_ref(s), p]


def translate(p, g, n, forward=True):
    source = control if forward else step
    go = lambda r, h=g, m=n: translate(r, h, m, forward)
    match p:
        case ['hyp', _]:
            return p
        case ['succ', c, a, h] if forward:
            previous = a if c == Z else ['i', c, a, h]
            return ev(ref(previous), ref(['i', ['s', c], a, h]))
        case ['tr', h, p, q] if forward:
            return congruence(h, go(p), go(q), g, n)
        case ['refl', a] if not forward:
            return control_ref(a)
        case ['ev', p, q] if not forward:
            _, b, _ = source.infer(q, g, n)
            _, c, a, h = b
            cp = ['succ', c[1], a, h]
            middle = ['tr', h, go(p), control_sym(cp, g, n)]
            return ['tr', V, middle, go(q)]
        case ['qe', t, p, q]:
            return ['qe', t, go(p), go(q)]
        case ['de', a, p, q]:
            b = source.infer(p, g, n)
            local = [['q', b[1]]] + [source.shift(x) for x in g]
            return ['de', a, go(p), go(q, local, n + 1)]
        case ['di', b, t, p]:
            a = source.sub(['q', b], t)[1]
            h = a if a[0] == '=' and t == Z else source.shift(source.sub(a, Z))
            local = [h] + [source.shift(x) for x in g]
            return ['di', b, t, go(p, local, n + 1)]
        case _:
            raise ValueError('Unknown source rule')


def translate_certificate(c, forward=True):
    source, target = (control, step) if forward else (step, control)
    source.check(c)
    out = dict(c, proof=translate(c['proof'], c['context'], c['variables'], forward))
    target.check(out)
    return out
