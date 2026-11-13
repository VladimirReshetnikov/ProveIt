"""Untrusted persistent proof builders for the numerical-argument-free kernel.

The arithmetic constructors and conditional-copy construction are adapted
from ProveIt's conditional_copy package, pinned in SOURCE_PROVENANCE.json.
Every completed construction is replayed by checker.py.  In particular,
Use antecedents are builders, never finished proofs weakened into a new
scope.  This distinction is needed because Close selects the newest name.
"""
from checker import walk, sub, prove, need

INITIAL = [([], [1, 1])]
X, Y, V, W, U, Z = [-100001 - j for j in range(6)]


def nf(a):
    return walk(a, lambda i, d: i)


def shift(a, k):
    return walk(a, lambda i, d: i + k if i > d else i)


def raw_map(a, f, d=0):
    if type(a) is int:
        return f(a, d)
    return [raw_map(b, f, d + 2 * (len(a) != 2 and j == len(a) - 1))
            for j, b in enumerate(a)]


def bind(a, names):
    return raw_map(a, lambda i, d:
                   d + len(names) - names.index(i) if i in names
                   else i + len(names) if i > d else i)


def at(a, name, value):
    return walk(a, lambda i, d: shift(value, d) if i == name else i)


def S(a):
    return [0, a, 0]


ONE, TWO = S(0), S(S(0))


def P(a):
    return nf([a, 0, 2])


def C(n, a, b):
    return P([n, a, S(shift(b, 2))])


def D(a, x=X, y=Y):
    return nf([bind(a, [x, y])])


def gate(y, A):
    if len(A) == 2:
        return [C(y, 0, A[0]), C(y, 0, A[1])]
    return [gate(shift(y, 2), A[0])]


def select(y, A, B):
    need(len(A) == len(B))
    if len(A) == 2:
        return [C(y, A[0], B[0]), C(y, A[1], B[1])]
    return [select(shift(y, 2), A[0], B[0])]


def hypothesis(index):
    """Use a retained unconditional constant clause, in any larger scope."""
    return [index, None]


def vacuous(t, g):
    """V_t = D_x,y(x=t), by Close and its constant hypothesis."""
    t = nf(t)
    result = [[2, t], hypothesis(len(g))]
    need(prove(result, g) == [[2, t]])
    return result


def use(g, index, t=0, antecedent=None):
    """Arbitrary specialization, with a persistent antecedent builder.

    antecedent(local_context) returns a proof of the clause's unchanged
    antecedent in exactly local_context.  It is invoked after V_t opens
    a new numerical parameter.  Unconditional clauses require no builder.
    """
    t = nf(t)
    b = -len(g)
    major = vacuous(t, g)
    local = g + [([b, t], [b, t])]
    base, body = g[index]
    premise = antecedent(local) if base else None
    result = [[], major, [index, premise]]
    need(prove(result, g) == sub(body, t))
    return result


def refl(g, t):
    return use(g, 0, t)


def intro_context(A, g):
    b = -len(g)
    B = sub(A[0], b + 1, 1)
    base = sub(B, 0)
    hyp = sub(B, b) if base == [0, 0] else base
    return g + [([], hyp)], sub(B, S(b))


def truth(A, g):
    if len(A) == 2:
        need(A == [0, 0])
        return refl(g, 0)
    local, goal = intro_context(A, g)
    branch = (hypothesis(len(g)) if goal == local[-1][1]
              else truth(goal, local))
    result = [A[0], branch]
    need(prove(result, g) == A)
    return result


def delta(s, H):
    """D_x,y Sel(y,H(s),H(x)), with V the placeholder in H."""
    return D(select(Y, at(H, V, s), at(H, V, X)))


def delta_proof(s, H, g=INITIAL):
    """Conditional copy, using no supplied witness or specialization."""
    closure = D(gate(W, delta(P(W), H)), U, W)
    outer, inner_goal = intro_context(closure, g)
    newest = -len(g)
    need(inner_goal == delta(newest, H))
    inner, identity_goal = intro_context(inner_goal, outer)
    if len(identity_goal) == 2 and identity_goal[0] == identity_goal[1]:
        identity = refl(inner, identity_goal[0])
    else:
        need(inner[-1][1] == identity_goal)
        identity = hypothesis(len(outer))
    major = [closure[0], [inner_goal[0], identity]]
    need(prove(major, g) == closure)
    body = sub(closure[0], newest, 1)
    local = g + [(sub(body, 0), body)]
    base = local[-1][0]
    branch = use(local, len(g), S(s), lambda enlarged: truth(base, enlarged))
    result = [[], major, branch]
    need(prove(result, g) == delta(s, H))
    return result


def arbitrary_intro(B, t, step_builder, g=INITIAL):
    """Recover liberal Close using a regenerated source-premise builder."""
    goal = [B]
    H = [sub(B, V, 1)]

    def h_proof(context):
        Ht = at(H, V, t)
        local, target = intro_context(Ht, context)
        result = [Ht[0], step_builder(local, target)]
        need(prove(result, context) == Ht)
        return result

    transfer = delta_proof(t, H, g)
    transfer_goal = prove(transfer, g)
    b = -len(g)
    body = sub(transfer_goal[0], b, 1)
    opened = g + [(sub(body, 0), body)]
    local, step_goal = intro_context(goal, opened)
    z = -len(opened)
    hb = use(local, len(g), ONE, h_proof)
    hb_goal = prove(hb, local)
    c = -len(local)
    hb_body = sub(hb_goal[0], c, 1)
    hb_opened = local + [(sub(hb_body, 0), hb_body)]
    base = hb_opened[-1][0]
    if len(base) == 2 and base[0] == base[1]:
        base_builder = lambda enlarged: refl(enlarged, base[0])
    else:
        need(base == local[-1][1])
        base_builder = lambda enlarged: hypothesis(len(opened))
    output = use(hb_opened, len(local), S(z), base_builder)
    step = [[], hb, output]
    need(prove(step, local) == step_goal)
    introduced = [B, step]
    need(prove(introduced, opened) == goal)
    result = [[], transfer, introduced]
    need(prove(result, g) == goal)
    return result
