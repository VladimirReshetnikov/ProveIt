"""Untrusted named-syntax certificate constructors for the R kernel.

No part of this module is imported by kernel.py.
"""
from dataclasses import dataclass
from itertools import count

names = count()


def fresh(prefix='v'):
    return prefix + str(next(names))


Z = ('zero',)


def V(x): return ('var', x)
def S(x): return ('succ', x)
def Eq(s, t): return ('eq', s, t)
def Q(y, b): return ('q', y, b)
def D(x, y, b): return ('d', x, y, b)


def R(n, a, update):
    u, v = fresh('u'), fresh('v')
    return ('rec', n, a, u, v, update(V(u), V(v)))


def num(n):
    r = Z
    for _ in range(n): r = S(r)
    return r


def subst(t, x, image):
    tag, *a = t
    if tag == 'zero': return t
    if tag == 'var': return image if a[0] == x else t
    if tag == 'succ': return S(subst(a[0], x, image))
    if tag == 'rec':
        n, seed, u, v, body = a
        return ('rec', subst(n, x, image), subst(seed, x, image), u, v,
                body if x in (u, v) else subst(body, x, image))
    if tag == 'eq': return Eq(*(subst(b, x, image) for b in a))
    if tag == 'q':
        y, b = a
        return t if x == y else Q(y, subst(b, x, image))
    if tag == 'd':
        w, y, b = a
        return t if x in (w, y) else D(w, y, subst(b, x, image))
    raise ValueError(t)


def encode(t, rho=(), rigid=None):
    """Canonical odd coordinates; placeholders occupy genuine zero slots."""
    rigid = {} if rigid is None else rigid
    tag, *a = t
    if tag == 'zero': return 0
    if tag == 'var':
        x, = a
        return rigid[x] if x in rigid else 2 * rho.index(x) + 1
    if tag == 'succ': return [encode(a[0], (None,) + rho, rigid)]
    if tag == 'rec':
        n, seed, u, v, body = a
        return [encode(n, (None, None) + rho, rigid),
                encode(seed, (None, None) + rho, rigid),
                encode(body, (v, u) + rho, rigid)]
    if tag == 'eq': return [encode(b, rho, rigid) for b in a]
    if tag == 'q':
        y, b = a
        return [encode(b, (y,) + rho, rigid)]
    if tag == 'd':
        x, y, b = a
        return [0, 0, encode(b, (y, x) + rho, rigid)]
    raise ValueError(t)


def free(t):
    tag, *a = t
    if tag == 'zero': return set()
    if tag == 'var': return {a[0]}
    if tag == 'succ': return free(a[0])
    if tag == 'rec':
        n, seed, u, v, body = a
        return free(n) | free(seed) | (free(body) - {u, v})
    if tag == 'eq': return free(a[0]) | free(a[1])
    if tag == 'q': return free(a[1]) - {a[0]}
    if tag == 'd': return free(a[2]) - set(a[:2])
    raise ValueError(t)


def same(s, t):
    env = {x: -i-1 for i, x in enumerate(sorted(free(s) | free(t)))}
    return encode(s, rigid=env) == encode(t, rigid=env)


def W(t): return R(t, Z, lambda u, v: u)


def J(n, a, h):
    return W(R(n, a, lambda u, v: S(h(u, W(v)))))


@dataclass
class Proof:
    goal: tuple
    rule: str
    data: tuple = ()


def hyp(f): return Proof(f, 'hyp')


def computation(r):
    tag, n, a, u, v, body = r
    assert tag == 'rec'
    if n == Z:
        rhs = S(a)
    else:
        assert n[0] == 'succ'
        counter = n[1]
        old = ('rec', counter, a, u, v, body)
        rhs = subst(subst(body, u, counter), v, old)
    return Proof(Eq(r, rhs), 'compute')


def transport(major, x, motive, minor):
    _, s, t = major.goal
    # Equality here is checked after encoding, so alpha-renaming is immaterial.
    assert same(subst(motive, x, s), minor.goal)
    return Proof(subst(motive, x, t), 'transport', (major, x, motive, minor))


def refl(t):
    p = computation(W(S(t)))
    x = fresh('h')
    return transport(p, x, Eq(V(x), t), p)


def congruence(p, f):
    _, s, t = p.goal
    x = fresh('h')
    return transport(p, x, Eq(f(s), f(V(x))), refl(f(s)))


def symmetry(p):
    _, s, t = p.goal
    x = fresh('h')
    return transport(p, x, Eq(V(x), s), refl(s))


def trans(p, q):
    _, s, t = p.goal
    _, u, v = q.goal
    assert same(t, u)
    x = fresh('h')
    return transport(q, x, Eq(s, V(x)), p)


def j_zero(a, h):
    inner = R(Z, a, lambda u, v: S(h(u, W(v))))
    p = congruence(computation(inner), W)
    return trans(p, computation(W(S(a))))


def j_successor(n, a, h):
    inner = R(S(n), a, lambda u, v: S(h(u, W(v))))
    p = congruence(computation(inner), W)
    # p's right side is W(S(h(n,J(n,a)))).
    return trans(p, computation(p.goal[2]))


def qe(major, target, base):
    _, y, body = major.goal
    assert same(subst(body, y, Z), base.goal)
    return Proof(subst(body, y, target), 'qe', (major, target, base))


def de(major, eigen, continuation):
    return Proof(continuation.goal, 'de', (major, eigen, continuation))


def di(formula, witness, eigen, step, induction=True):
    _, x, y, body = formula
    target = subst(subst(body, x, witness), y, S(V(eigen)))
    assert same(target, step.goal)
    return Proof(formula, 'di', (witness, eigen, step, induction))


def closure(y, body, step_builder, induction=True):
    """DI with an unused existential coordinate, then DE and hypothesis use."""
    x, z, w = fresh('unused'), fresh('eigen'), fresh('witness')
    formula = D(x, y, body)
    premise = step_builder(V(z))
    major = di(formula, num(1), z, premise, induction)
    result = Q(y, body)
    return de(major, w, hyp(result))


def prove_instance(y, body, base, step_builder, target, induction=True):
    return qe(closure(y, body, step_builder, induction), target, base)


def packet(proof):
    """Emit instructions in the kernel's actual global freshness order."""
    floor = 0

    def emit(p, rigid):
        nonlocal floor
        if p.rule == 'hyp': return []
        if p.rule == 'compute': return [[0, 0]]
        if p.rule == 'transport':
            major, x, motive, minor = p.data
            cell = [encode(major.goal, rigid=rigid), encode(motive, (x,), rigid)]
            return [cell] + emit(major, rigid) + emit(minor, rigid)
        if p.rule == 'qe':
            major, target, base = p.data
            cell = [encode(major.goal, rigid=rigid), encode(target, rigid=rigid)]
            return [cell] + emit(major, rigid) + emit(base, rigid)
        if p.rule == 'de':
            major, eigen, continuation = p.data
            cells = [[encode(major.goal, rigid=rigid), 0]] + emit(major, rigid)
            floor -= 1
            return cells + emit(continuation, {**rigid, eigen: floor})
        if p.rule == 'di':
            witness, eigen, step, induction = p.data
            cell = [0 if induction else [], encode(witness, rigid=rigid)]
            floor -= 1
            return [cell] + emit(step, {**rigid, eigen: floor})
        raise ValueError(p.rule)

    cells = emit(proof, {})
    return cells[::-1] + [encode(proof.goal)]


def evaluate(term, environment=None):
    """Independent numerical evaluator, for finite standard-number tests only."""
    environment = {} if environment is None else environment
    tag, *a = term
    if tag == 'zero': return 0
    if tag == 'var': return environment[a[0]]
    if tag == 'succ': return evaluate(a[0], environment) + 1
    if tag == 'rec':
        n, seed, u, v, body = a
        count_ = evaluate(n, environment)
        state = evaluate(seed, environment) + 1
        for counter in range(count_):
            state = evaluate(body, {**environment, u: counter, v: state})
        return state
    raise ValueError('Not a numerical term')
