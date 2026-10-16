"""Independent PSC alpha checks and algebraic controls; no machine/Lean build.

The reference uses the curried form of the accepted six-fresh-label PSC
wrapper. Currying is an ordinary classical equivalence, not a proved
translation for the retained coded calculus.
"""
from itertools import product
from functools import cache
from math import isqrt

M = lambda i, j: ('m', i, j)
A = lambda i, p: ('a', i, p)
E = lambda i, p: ('e', i, p)
I = lambda p, q: ('i', p, q)
O = lambda p, q: ('o', p, q)
J = lambda p, q: ('j', p, q)
B = ('b',)
S = lambda x, y, z: A(z, I(M(z, x), M(z, y)))


def codec_checks(limit=100000):
    """Check normalization, not a false roundtrip for Bottom aliases."""
    if not __debug__:
        raise RuntimeError('run without -O: this audit requires assertions')
    @cache
    def decode(n):
        if n == 0:
            return ('t',)
        tag = n % 4
        if tag == 1:
            return B
        p = n // 4
        diagonal = (isqrt(8*p+1)-1)//2
        right = p-diagonal*(diagonal+1)//2
        left = diagonal-right
        if tag == 2:
            return M(left, right)
        return I(decode(left), decode(right)) if tag == 0 else A(left, decode(right))

    def encode(p):
        pair = lambda a, b: (a+b)*(a+b+1)//2+b
        if p[0] == 't': return 0
        if p[0] == 'b': return 1
        if p[0] == 'm': return 4*pair(p[1],p[2])+2
        if p[0] == 'i': return 4*pair(encode(p[1]),encode(p[2]))
        return 4*pair(p[1],encode(p[2]))+3

    def labels(p):
        if p[0] in ('b','t'): return set()
        if p[0] == 'm': return set(p[1:])
        if p[0] == 'a': return {p[1]} | labels(p[2])
        return labels(p[1]) | labels(p[2])

    for n in range(limit):
        p = decode(n)
        assert decode(encode(p)) == p
        assert all(i < n for i in labels(p))
        assert all(i < n+2 for i in labels(p))
    assert decode(5) == B and encode(decode(5)) == 1
    return {'numeric_codes':limit, 'normalization_roundtrips':True,
            'all_variable_labels_below_code':True, 'bottom_alias_5_normalizes_to_1':True}


def rename_free(p, mapping, bound=frozenset()):
    if p[0] == 'm':
        return M(*(v if v in bound else mapping.get(v, v) for v in p[1:]))
    if p[0] in 'ae':
        return (p[0], p[1], rename_free(p[2], mapping, bound | {p[1]}))
    if p[0] in 'ioj':
        return (p[0], rename_free(p[1], mapping, bound),
                rename_free(p[2], mapping, bound))
    return p


def alpha(p, env=()):
    def var(i):
        return ('bound', env.index(i)) if i in env else ('free', i)
    if p[0] == 'm':
        return ('m', var(p[1]), var(p[2]))
    if p[0] in 'ae':
        return (p[0], alpha(p[2], (p[1],) + env))
    if p[0] in 'ioj':
        return (p[0], alpha(p[1], env), alpha(p[2], env))
    return p


def fixed(p, k):
    """k is fresh for p and distinct from designated matrix slots 0/1."""
    sb = A(0, E(k, A(1, I(p, S(1, k, 0)))))
    guard = O(S(0, 1, k), M(0, k))
    closed = A(0, I(guard, A(1, I(p, M(1, k)))))
    support = A(1, I(M(1, k), E(0, p)))
    return I(sb, A(1, E(k, J(closed, support))))


def reference(p, maximum_label):
    """Independent six-fresh-label version, renaming free matrix slots only."""
    x, y, z, bound, seed, hull = range(maximum_label + 1, maximum_label + 7)
    matrix = rename_free(p, {0: x, 1: y})
    sb = A(x, E(bound, A(y, I(matrix, S(y, bound, z)))))
    guard = O(S(x, seed, z), M(x, hull))
    closed = A(x, I(guard, A(y, I(matrix, M(y, hull)))))
    support = A(y, I(M(y, hull), E(x, matrix)))
    return I(sb, A(seed, E(hull, J(closed, support))))


def matrices(c):
    atoms = [B] + [M(i, j) for i in range(c) for j in range(c)]
    forms = atoms + [q(i, p) for i in range(c) for p in atoms for q in (A, E)]
    forms += [q(p, r) for p in atoms for r in atoms for q in (I, O, J)]
    forms += [A(0, E(1, I(p, A(0, r)))) for p in atoms for r in atoms]
    return forms


def finite_sat(p, env, relation, n):
    k = p[0]
    if k == 'b':
        return False
    if k == 'm':
        return relation[env[p[1]] * n + env[p[2]]]
    if k in 'ae':
        vals = []
        for x in range(n):
            changed = dict(env)
            changed[p[1]] = x
            vals.append(finite_sat(p[2], changed, relation, n))
        return all(vals) if k == 'a' else any(vals)
    x = finite_sat(p[1], env, relation, n)
    y = finite_sat(p[2], env, relation, n)
    return (not x or y) if k == 'i' else (x or y) if k == 'o' else (x and y)


def dead_quantifier_sat(p):
    """Algebraic logical-incompleteness control; not first-order semantics."""
    k = p[0]
    if k in ('b', 'm'):
        return False
    if k == 'a':
        return True
    if k == 'e':
        return False  # Exactly the implication-to-Bottom expansion.
    x, y = dead_quantifier_sat(p[1]), dead_quantifier_sat(p[2])
    return (not x or y) if k == 'i' else (x or y) if k == 'o' else (x and y)


def check():
    if not __debug__:
        raise RuntimeError('run without -O: this audit requires assertions')
    count = 0
    for c in (2, 3, 4, 5):
        for p in matrices(c):
            assert alpha(fixed(p, c)) == alpha(reference(p, c))
            assert alpha(fixed(p, c + 2)) == alpha(reference(p, c))
            assert dead_quantifier_sat(fixed(p, c + 2))
            count += 1
    # Freshness cannot be weakened: k=2 captures the parameter of phi=M(2,0).
    relation = (False, False, False, True)  # domain {0,1}; only 1 membership 1.
    env = {i: 0 for i in range(9)}
    env[2] = 1
    assert finite_sat(fixed(M(2, 0), 2), env, relation, 2)
    assert not finite_sat(reference(M(2, 0), 2), env, relation, 2)
    # Constant-true universal operators validate the retained quantifier rows,
    # even though Bottom is false. This refutes a completeness inference.
    for p, q in product(matrices(2), repeat=2):
        rho2 = I(A(0, I(p, q)), I(A(0, p), A(0, q)))
        rho4 = I(A(0, A(1, p)), A(1, A(0, p)))
        rho6 = I(E(0, A(0, p)), p)
        vacuity = I(M(0, 1), A(2, M(0, 1)))
        assert all(map(dead_quantifier_sat, (rho2, rho4, rho6, vacuity)))
    # Check the ACTUAL frozen252 C/G/V bundle, instead of projecting this
    # countermodel onto an unrelated theory. C and G start with existential
    # quantifiers, so they are false when every universal is constant true.
    import theory_backend_experiment as t
    spec, _ = t.published_spec()

    def actual_sat(p, env):
        if p == 0:
            return True
        if p == 1:
            return False
        if isinstance(p, str):
            return env[p]
        kind, a, b = p
        if kind == 'all':
            return True
        if kind == 'rel':
            return False
        assert kind == 'imp'
        return not actual_sat(a, env) or actual_sat(b, env)

    rows = spec['ax_rows']('a', 'h', 'b', 'c', 'u')
    original = rows[3]
    dual = t.Imp('b', t.All('a', t.Ex('a', 'b')))
    cp = spec['bundle_C']('a', 'b', 'c')
    gic = spec['bundle_G']('a', 'b', 'c')
    vac = t.Imp(t.Rel('a', 'b'), t.All('c', t.Rel('a', 'b')))
    frozen_bundle = t.And(vac, t.And(cp, gic))
    actual_cases = 0
    for bits in product((False, True), repeat=5):
        env = dict(zip(('a', 'h', 'b', 'c', 'u'), bits))
        assert all(actual_sat(rows[i], env) for i in (0, 1, 5, 7))
        assert actual_sat(original, env) and actual_sat(dual, env)
        assert actual_sat(vac, env)
        assert not actual_sat(cp, env) and not actual_sat(gic, env)
        assert not actual_sat(frozen_bundle, env)
        actual_cases += 1
    return {'alpha_cases': count, 'both_k_c_and_k_c_plus_2': True,
            'freshness_semantic_negative_control': True,
            'dead_quantifier_incompleteness_control': True,
            'actual_frozen252_boolean_cases': actual_cases,
            'dead_quantifiers_model_actual_frozen252_bundle': False}


if __name__ == '__main__':
    import json
    print(json.dumps(check(), indent=2))
