"""Finite proof constructions and independent counter-recursor semantics.

These helpers are not imported by the standalone acceptance module.
"""

def R(n, a, h):
    return [n, a, 0 if n == 0 else h]


def S(n):
    return R(0, n, 0)


def lift(a, count, depth=0):
    if type(a) is int:
        return a + count if a > depth else a
    n, seed, h = a
    return R(lift(n, count, depth), lift(seed, count, depth), lift(h, count, depth + 2))


def instantiate(a, values, new_count=0, depth=0):
    """Simultaneous replacement of outer bound slots, retaining inner slots.

    The values are in a context with new_count replacement slots. External
    indices move by new_count-len(values). Unlike the kernel implementation,
    this function replaces all slots in one recursive traversal and lifts
    inserted values beneath inner binders.
    """
    if type(a) is int:
        if a <= depth:
            return a
        index = a - depth - 1
        if index < len(values):
            return lift(values[index], depth)
        return a + new_count - len(values)
    n, seed, h = a
    return R(instantiate(n, values, new_count, depth),
             instantiate(seed, values, new_count, depth),
             instantiate(h, values, new_count, depth + 2))


def P(n):
    return R(n, 0, 2)


def C(n, a, b):
    return P(R(n, a, S(lift(b, 2))))


def Rec(n, a, h):
    return P(R(n, a, S(instantiate(h, [P(1), 2], 2))))


def term_value(a, free=None, bound=(), fuel=None):
    free = {} if free is None else free
    fuel = [100000] if fuel is None else fuel
    fuel[0] -= 1
    if fuel[0] < 0:
        raise OverflowError('semantic test fuel')
    if type(a) is int:
        return 0 if a == 0 else free[a] if a < 0 else bound[a - 1]
    n, seed, h = a
    counter = term_value(n, free, bound, fuel)
    state = term_value(seed, free, bound, fuel) + 1
    if counter > 300:
        raise OverflowError('semantic test counter')
    for i in range(counter):
        state = term_value(h, free, (state, i) + bound, fuel)
    return state


def proof(eq, tree):
    return (eq, tree)


def refl(a):
    return proof([a, a], ['r', a])


def ce(p, q):
    s, t = p[0]
    b, r = q[0]
    n, a, h = b
    if n != S(s):
        raise ValueError('generator source mismatch')
    value = instantiate(h, [R(t, a, h), t])
    return proof([r, value], ['v', p[1], q[1]])


def computation(n, a, h):
    return ce(refl(n), refl(R(S(n), a, h)))


def root(p, q):
    if p[0][0] != q[0][0]:
        raise ValueError('generator root mismatch')
    anchor = P(S(p[0][0]))
    return ce(p, ce(q, refl(anchor)))


def symmetry(p):
    return root(refl(p[0][0]), p)


def trans(p, q):
    if p[0][1] != q[0][0]:
        raise ValueError('generator transitivity mismatch')
    return root(q, symmetry(p))


def congruence(h, p):
    s, t = p[0]
    body = instantiate(h, [2], 2)
    bridge = R(S(s), 0, body)
    return ce(p, ce(refl(s), refl(bridge)))


def transport(h, p, q):
    return root(congruence(h, p), q)


def hypothesis(eq, index):
    return proof(eq, ['u', index, 0, ['r', 0]])


def c_zero(a, b):
    return computation(a, 0, 2)


def c_step(n, a, b):
    first = computation(n, a, S(lift(b, 2)))
    return trans(congruence(P(1), first), computation(b, 0, 2))


def rec_zero(a, h):
    return computation(a, 0, 2)


def rec_step(n, a, h):
    body = S(instantiate(h, [P(1), 2], 2))
    first = computation(n, a, body)
    result = instantiate(h, [Rec(n, a, h), n])
    return trans(congruence(P(1), first), computation(result, 0, 2))


def nodes(tree):
    if tree[0] == 'r':
        return 1
    if tree[0] == 'v':
        return 1 + nodes(tree[1]) + nodes(tree[2])
    if tree[0] in ('u', 'i'):
        return 1 + nodes(tree[3])
    if tree[0] == 'e':
        return 1 + nodes(tree[2]) + nodes(tree[3])
    raise ValueError(tree[0])


def standard_identity(n):
    return Rec(n, 0, S(1))


def induction_certificate(target):
    equation = [standard_identity(1), 1]
    goal = [equation]
    z = -1
    hypothesis_z = hypothesis([standard_identity(z), z], 0)
    step = trans(rec_step(z, 0, S(1)), congruence(S(1), hypothesis_z))
    induction = ['i', goal, 0, step[1]]
    result = [standard_identity(target), target]
    use = ['u', 0, target, rec_zero(0, S(1))[1]]
    tree = ['e', result, induction, use]
    return {'goal': result, 'proof': tree}


def random_term(rng, depth, height, free=0):
    atoms = [0] + list(range(1, depth + 1)) + list(range(-free, 0))
    if height == 0 or rng.randrange(3) == 0:
        return rng.choice(atoms)
    return R(random_term(rng, depth, height - 1, free),
             random_term(rng, depth, height - 1, free),
             random_term(rng, depth + 2, height - 1, free))


