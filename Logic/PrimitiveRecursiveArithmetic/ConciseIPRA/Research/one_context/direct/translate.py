"""Untrusted proof compiler. Neither standalone checker imports this module."""
import native_checker as native
import one_context_checker as one


def native_refl(t):
    p = ['zero', t, ['z']]
    return ['tr', ['v', 0], native.shift(t), p, p]


def native_symmetry(p, left):
    return ['tr', ['v', 0], native.shift(left), p, native_refl(left)]


def translate(p, source, g, n):
    kernel = native if source == 'native' else one
    tag = p[0]
    if tag in ['hyp', 'zero', 'succ']:
        return p
    if tag == 'tr':
        if source == 'native':
            _, a, b, major, minor = p
            major = translate(major, source, g, n)
            minor = translate(minor, source, g, n)
            return ['tr', b, major, ['tr', a, major, minor]]
        _, a, major, minor = p
        e = kernel.infer(major, g, n)
        f = kernel.infer(minor, g, n)
        major = translate(major, source, g, n)
        minor = translate(minor, source, g, n)
        old_transport = ['tr', a, kernel.shift(f[2]), major, minor]
        return native_symmetry(old_transport, kernel.sub(a, e[2]))
    if tag == 'qe':
        _, t, major, minor = p
        return ['qe', t, translate(major, source, g, n), translate(minor, source, g, n)]
    if tag == 'de':
        _, a, major, minor = p
        b = kernel.infer(major, g, n)[1]
        extended = [['q', b]] + [kernel.shift(x) for x in g]
        return ['de', a, translate(major, source, g, n), translate(minor, source, extended, n + 1)]
    if tag == 'di':
        _, b, t, premise = p
        a = kernel.sub(['q', b], t)[1]
        extended = [kernel.shift(kernel.sub(a, ['z']))] + [kernel.shift(x) for x in g]
        return ['di', b, t, translate(premise, source, extended, n + 1)]
    if tag == 'qi':
        _, e, premise = p
        extended = [e] + [kernel.shift(x) for x in g]
        return ['qi', e, translate(premise, source, extended, n + 1)]
    raise ValueError('Unknown proof constructor')


def translate_certificate(c, source):
    kernel = native if source == 'native' else one
    kernel.check(c)
    return dict(c, proof=translate(c['proof'], source, c['context'], c['variables']))
