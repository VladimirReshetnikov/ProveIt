"""Untrusted proof constructors for the zero-normal deterministic clause checker.

No theorem is accepted here.  Every returned proof must be replayed through
the standalone checker.  Equational proofs are triples (left, right, tree).
Positive integers are bound indices; negative integers are free levels.
All supplied ordinary terms have no dangling positive bound indices.
"""

ZERO = 0
ONE = ['s', 0]


def S(a):
    return ['s', a]


def I(n, a, h):
    return a if n == 0 else ['i', n, a, h]


def Eq(a, b):
    return ['=', a, b]


def opening(a, value, depth=0):
    """Independent structural opening; value is locally closed."""
    if type(a) is int:
        if a <= depth:
            return a
        return value if a == depth + 1 else a - 1
    tag = a[0]
    if tag == 's':
        return S(opening(a[1], value, depth))
    if tag == 'i':
        return I(opening(a[1], value, depth),
                 opening(a[2], value, depth),
                 opening(a[3], value, depth + 1))
    if tag == '=':
        return Eq(opening(a[1], value, depth),
                  opening(a[2], value, depth))
    if tag == 'd':
        return ['d', opening(a[1], value, depth + 2)]
    raise ValueError(('unknown syntax', a))


def abstract(a, marker, depth=0):
    """Bind one distinguished negative free level, leaving other levels free.

    Any pre-existing dangling positive index is shifted to make room for the
    new binder.  Internal iterator and D binders remain capture-safe.
    """
    if type(a) is int:
        return depth + 1 if a == marker else a + (a > depth)
    tag = a[0]
    if tag == 's':
        return S(abstract(a[1], marker, depth))
    if tag == 'i':
        return I(abstract(a[1], marker, depth),
                 abstract(a[2], marker, depth),
                 abstract(a[3], marker, depth + 1))
    if tag == '=':
        return Eq(abstract(a[1], marker, depth),
                  abstract(a[2], marker, depth))
    if tag == 'd':
        return ['d', abstract(a[1], marker, depth + 2)]
    raise ValueError(('unknown syntax', a))


def refl(a):
    return a, a, ['r', a]


def equation(formula, proof):
    if not (isinstance(formula, list) and len(formula) == 3
            and formula[0] == '='):
        raise ValueError(('not an equation', formula))
    return formula[1], formula[2], proof


def step(p, q):
    """One primitive successor Step, computing its conclusion."""
    lhs, rhs, minor = q
    if not (isinstance(lhs, list) and len(lhs) == 4 and lhs[0] == 'i'
            and isinstance(lhs[1], list) and len(lhs[1]) == 2
            and lhs[1][0] == 's'):
        raise ValueError(('not a successor iterate', lhs))
    n, a, h = lhs[1][1], lhs[2], lhs[3]
    if p[0] != I(n, a, h):
        raise ValueError(('wrong predecessor', p[0], I(n, a, h)))
    return rhs, opening(h, p[1]), ['x', p[2], minor]


def comp(n, a, h):
    """I(S n,a;h) = h(I(n,a;h)), with zero iteration canonical."""
    return step(refl(I(n, a, h)), refl(I(S(n), a, h)))


def pivot(p, q):
    """From p:s=t and q:s=r, derive r=t without scope extension."""
    if p[0] != q[0]:
        raise ValueError(('pivot source mismatch', p[0], q[0]))
    frame = I(ONE, p[0], 1)
    return step(p, step(q, refl(frame)))


def sym(p):
    return pivot(refl(p[0]), p)


def trans(p, q):
    if p[1] != q[0]:
        raise ValueError(('transitivity mismatch', p[1], q[0]))
    return pivot(q, sym(p))


def cross(p, q, h):
    """From p:s=t and q:h(s)=r derive r=h(t); h binds index 1."""
    if q[0] != opening(h, p[0]):
        raise ValueError(('crossed transport mismatch', q[0], opening(h, p[0])))
    bridge = trans(comp(0, p[0], h), q)
    return step(p, bridge)


def congruence(p, h):
    """From s=t derive h(s)=h(t)."""
    return cross(p, refl(opening(h, p[0])), h)


def transport_equation(p, q, template):
    """From s=t and F(s), with F an equation template, derive F(t)."""
    if not (isinstance(template, list) and len(template) == 3
            and template[0] == '='):
        raise ValueError(('not an equation template', template))
    if Eq(q[0], q[1]) != opening(template, p[0]):
        raise ValueError(('equation transport mismatch', Eq(q[0], q[1]),
                          opening(template, p[0])))
    intermediate = cross(p, q, template[1])
    return cross(p, intermediate, template[2])


def selector(v, a, b):
    """C(v,a,b), with locally closed b as a constant iterator update."""
    return I(v, a, b)


def name(t, scope):
    """Construct Name_t = D_x,y (C(y,0,x)=C(y,0,t))."""
    matrix = Eq(I(1, 0, 3), I(1, 0, t))
    goal = ['d', matrix]
    fresh = -scope - 1
    conclusion = I(S(fresh), 0, t)
    return goal, ['i', goal, t, refl(conclusion)[2]]


def naming_clause(b, t):
    return Eq(0, 0), Eq(I(1, 0, b), I(1, 0, t))


def extract_name(b, t, at_one_proof):
    """Convert a proof of C(1,0,b)=C(1,0,t) to b=t arithmetically."""
    left = I(ONE, 0, b)
    right = I(ONE, 0, t)
    link = left, right, at_one_proof
    return trans(trans(sym(comp(0, 0, b)), link), comp(0, 0, t))


def newest_name_equality(b, t):
    """Use a naming clause currently at index zero, hence at target 1."""
    return extract_name(b, t, ['u', 0, refl(0)[2]])


def assumption(index):
    """Read [0=0 ; y.A] at any position; A is independent of its y."""
    return ['u', index, refl(0)[2]]


def fixture(p):
    return {'goal': Eq(p[0], p[1]), 'proof': p[2]}
