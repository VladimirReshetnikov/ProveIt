"""Untrusted constructors: emit ordinary certificates for counter_name3_matched."""
from copy import deepcopy
import counter_name3_matched as kernel

X, Y, U, V, W = -100001, -100002, -100003, -100004, -100005
ONE = [0, 0, 0]
TWO = [0, ONE, 0]
INITIAL = [([], [1, 1])]


def normal(a):
    return kernel.walk(a, lambda i, d: i)


def map_raw(a, function, depth=0):
    if type(a) is int:
        return function(a, depth)
    size = len(a)
    return [map_raw(t, function, depth + 2 * (size != 2 and j == size - 1))
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
    return [0, a, 0]


def R(n, a, i, u, h):
    return normal([n, a, bind(h, [i, u])])


def P(n):
    return R(n, 0, U, V, U)


def C(n, a, b):
    return P(R(n, a, U, V, S(b)))


def K(n):
    return C(P(n), ONE, 0)


def J(n, a, i, u, h):
    return P(R(n, a, i, V, S(at(h, u, P(V)))))


def D(body, x=X, y=Y):
    return normal([bind(body, [x, y])])


def refl(t):
    return ['u', 0, normal(t), None]


def use(j, t, premise=None):
    return ['u', j, normal(t), premise]


def weaken(p, old_length, extra=1):
    def rename(a):
        if type(a) is int:
            return a - extra if a <= -old_length else a
        return [rename(t) for t in a]
    if p is None:
        return None
    match p:
        case ['u', j, t, q]:
            return ['u', j + (extra if j >= old_length else 0), rename(t),
                    weaken(q, old_length, extra)]
        case ['i', body, t, q]:
            return ['i', rename(body), rename(t), weaken(q, old_length, extra)]
        case ['e', q, e, r]:
            return ['e', weaken(q, old_length, extra),
                    weaken(e, old_length, extra), weaken(r, old_length, extra)]
    raise ValueError('bad proof')


def numerical_cases(template, name, target, zero, successor_builder, context):
    matrix = bind(template, [X, name])
    b = -len(context)
    body = kernel.sub(matrix, ONE, 1)
    local = context + [([], kernel.sub(body, 0))]
    major = ['i', matrix, ONE, successor_builder(b, local)]
    branch = use(len(context), target, weaken(zero, len(context)))
    proof = ['e', major, refl(b), branch]
    if kernel.prove(proof, context) != at(template, name, target):
        raise AssertionError('case mismatch')
    return proof


def transport(equality, equation, template, name, context=INITIAL):
    """From s=t and h(s)=r derive h(t)=r by the two-row packet."""
    source, target = kernel.prove(equality, context)
    left, right = kernel.prove(equation, context)
    if left != at(template, name, source):
        raise ValueError('template does not match equation')
    hx = at(template, name, X)
    packet = D([C(Y, 0, C(K(Y), hx, X)),
                C(Y, 0, C(K(Y), right, target))])
    b = -len(context)
    body = kernel.sub(packet[0], source, 1)
    base = kernel.sub(body, b if source == 0 else 0)
    local = context + [([], base)]
    step_template = [C(K(S(W)), left, source), C(K(S(W)), right, target)]
    zero = weaken(equality, len(context))
    def positive(fresh, extended):
        return weaken(equation, len(context), 2)
    step = numerical_cases(step_template, W, b, zero, positive, local)
    major = ['i', packet[0], source, step]
    alias = use(len(context), ONE, refl(0))
    branch = use(len(context), TWO, refl(0))
    proof = ['e', major, alias, branch]
    if kernel.prove(proof, context) != [at(template, name, target), right]:
        raise AssertionError('transport mismatch')
    return proof


def symmetry(eq, context=INITIAL):
    source, target = kernel.prove(eq, context)
    return transport(eq, refl(source), V, V, context)


def crossed_transport(eq, minor, template, name, context=INITIAL):
    return symmetry(transport(eq, minor, template, name, context), context)


def implication(antecedent, consequent, builder, context=INITIAL):
    packet = D([C(Y, antecedent[0], consequent[0]),
                C(Y, antecedent[1], consequent[1])])
    local = context + [([], antecedent)]
    branch = builder(use(len(context), 0), local)
    proof = ['i', packet[0], ONE, branch]
    if kernel.prove(proof, context) != packet:
        raise AssertionError('implication mismatch')
    return proof


def to_old(goal, p, g=INITIAL):
    """Translate a new proof to goal-directed full-R Name3 (see verifier)."""
    match p:
        case ['u', j, t, q]:
            return ['u', j, t, to_old(g[j][0], q, g) if g[j][0] else None]
        case ['i', body, t, q]:
            B = kernel.sub(body, t, 1)
            base = kernel.sub(B, -len(g) if len(body) == 2 and t == 0 else 0)
            target = kernel.sub(B, S(-len(g)))
            return ['i', t, to_old(target, q, g + [([], base)])]
        case ['e', q, e, r]:
            [body] = kernel.prove(q, g)
            B = kernel.sub(body, -len(g), 1)
            local = g + [(kernel.sub(B, 0), B)]
            _, t = kernel.prove(e, local)
            F = kernel.prove(r, local)
            return ['e', body, F, t, to_old([body], q, g),
                    to_old([-len(g), t], e, local), to_old(F, r, local)]
    raise ValueError('bad proof')
