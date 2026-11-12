"""Untrusted proof constructors for automatic witness specialization.

Only checker.py is trusted.  These helpers produce ordinary JSON certificates.
"""
from copy import deepcopy
import checker as kernel

X, Y, U, V = -100001, -100002, -100003, -100004
ONE = [0, 0]
TWO = [0, ONE]
TRUTH = [0, 0]
INITIAL = [([], [1, 1])]


def normal(a):
    return kernel.walk(a, lambda i, d: i)


def map_raw(a, variable, depth=0):
    if type(a) is int:
        return variable(a, depth)
    size = len(a)
    return [map_raw(t, variable, depth + (2 if size == 1 else int(size == 3 and j == 2)))
            for j, t in enumerate(a)]


def bind(a, names):
    def variable(i, d):
        if i in names:
            return d + len(names) - names.index(i)
        return i + len(names) if i > d else i
    return map_raw(a, variable)


def at(a, name, value):
    return kernel.walk(a, lambda i, d: value if i == name else i)


def S(a):
    return [0, a]


def I(n, a, name, h):
    return normal([n, a, bind(h, [name])])


def C(n, a, b):
    return I(n, a, U, b)


def parity(n):
    return I(n, 0, U, C(U, ONE, 0))


def D(body, x=X, y=Y):
    return normal([bind(body, [x, y])])


def refl(t):
    return ['u', 0, normal(t), None]


def use(index, target, premise=None):
    return ['u', index, normal(target), premise]


def weaken(proof, old_length, extra=1):
    """Insert unused context frames before the proof's local frames."""
    def rename(a):
        if type(a) is int:
            return a - extra if a <= -old_length else a
        return [rename(t) for t in a]
    if proof is None:
        return None
    tag = proof[0]
    if tag == 'u':
        _, j, t, p = proof
        return ['u', j + (extra if j >= old_length else 0), rename(t),
                weaken(p, old_length, extra)]
    if tag == 'i':
        return ['i', rename(proof[1]), rename(proof[2]),
                weaken(proof[3], old_length, extra)]
    if tag == 'e':
        return ['e', weaken(proof[1], old_length, extra),
                weaken(proof[2], old_length, extra)]
    raise ValueError('unknown proof constructor')


def numerical_cases(template, name, target, zero, successor_builder, context):
    """Derive a numerical case distinction using only u/i/e."""
    matrix = bind(template, [X, name])
    z = -len(context)
    body = kernel.sub(matrix, ONE, 1)
    local = context + [([], kernel.sub(body, 0))]
    step = successor_builder(z, local)
    major = ['i', matrix, ONE, step]
    branch = use(len(context), target, weaken(zero, len(context)))
    proof = ['e', major, branch]
    expected = at(template, name, target)
    if kernel.prove(proof, context) != expected:
        raise AssertionError('case constructor mismatch')
    return proof


def transport(equality, equation, template, name, context=INITIAL):
    """From s=t and h(s)=r construct a proof of h(t)=r.

    Row zero is 0=0. Row one is x=t. Row two is h(x)=r.
    All later positive rows alternate between those two equations.
    """
    source, target = kernel.prove(equality, context)
    left, right = kernel.prove(equation, context)
    if left != at(template, name, source):
        raise ValueError('transport template does not match source equation')
    hx = at(template, name, X)
    packet = D([C(Y, 0, C(parity(Y), hx, X)),
                C(Y, 0, C(parity(Y), right, target))])
    z = -len(context)
    opened = kernel.sub(packet[0], source, 1)
    base = kernel.sub(opened, z if source == 0 else 0)
    local = context + [([], base)]
    selector = [C(V, left, source), C(V, right, target)]
    zero = weaken(equation, len(context))
    def successor_builder(fresh, extended):
        return weaken(equality, len(context), 2)
    step = numerical_cases(selector, V, parity(S(z)), zero,
                           successor_builder, local)
    major = ['i', packet[0], source, step]
    branch = use(len(context), TWO, refl(0))
    proof = ['e', major, branch]
    expected = [at(template, name, target), right]
    if kernel.prove(proof, context) != expected:
        raise AssertionError('automatic transport mismatch')
    return proof


def symmetry(equality, context=INITIAL):
    source, target = kernel.prove(equality, context)
    return transport(equality, refl(source), V, V, context)


def crossed_transport(equality, equation, template, name, context=INITIAL):
    return symmetry(transport(equality, equation, template, name, context), context)


def implication(antecedent, consequent, builder, context=INITIAL):
    """A native D encoding of implication between two equations."""
    packet = D([C(Y, antecedent[0], consequent[0]),
                C(Y, antecedent[1], consequent[1])])
    local = context + [([], antecedent)]
    branch = builder(use(len(context), 0), local)
    proof = ['i', packet[0], ONE, branch]
    if kernel.prove(proof, context) != packet:
        raise AssertionError('implication constructor mismatch')
    return proof


def to_control(proof, context=INITIAL):
    """Exact derivation translation to the explicit-equality control."""
    tag = proof[0]
    if tag == 'u':
        _, j, t, premise = proof
        return ['u', j, t, to_control(premise, context) if context[j][0] else None]
    if tag == 'i':
        _, matrix, t, branch = proof
        body = kernel.sub(matrix, t, 1)
        base = kernel.sub(body, -len(context) if len(matrix) == 2 and not t else 0)
        return ['i', matrix, t, to_control(branch, context + [([], base)])]
    _, major, branch = proof
    formula = kernel.prove(major, context)
    b = -len(context)
    body = kernel.sub(formula[0], b, 1)
    base, pair = kernel.sub(body, 0), kernel.sub(body, ONE)
    local = context + [(base, body)]
    active = base == TRUTH and pair[0] == b
    equality = use(len(context), ONE, refl(0)) if active else refl(b)
    target = pair[1] if active else b
    specialized = kernel.walk(body, lambda i, d: target if i == b else i)
    return ['e', to_control(major, context), equality,
            to_control(branch, context + [(base, specialized)])]
