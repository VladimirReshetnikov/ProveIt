"""Untrusted proof constructors for checker.py; emitted trees are replayed by the kernel."""


from checker import walk, sub, prove, need


X, Y, V, W, U, Z = [-100001 - j for j in range(6)]


INITIAL = [([], [1, 1])]


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


def use(j, t=0, q=None):
    return [j, nf(t), q]


def refl(t):
    return use(0, t)


def intro_context(A, g):
    b = -len(g)
    B = sub(A[0], b + 1, 1)
    u = sub(B, 0)
    if u == [0, 0]:
        u = sub(B, b)
    return g + [([], u)], sub(B, S(b))


def truth(A, g):
    if len(A) == 2:
        need(A == [0, 0])
        return refl(0)
    local, goal = intro_context(A, g)
    if goal == local[-1][1]:
        branch = use(len(g))
    else:
        branch = truth(goal, local)
    p = [A[0], branch]
    need(prove(p, g) == A)
    return p


def delta(s, H):
    """D_x,y Sel(y,H(s),H(x)), with V the placeholder of H."""
    return D(select(Y, at(H, V, s), at(H, V, X)))


def delta_proof(s, H, g=INITIAL):
    """Prove Delta_s(H), with no equality premises and no Intro witness."""
    closure = D(gate(W, delta(P(W), H)), U, W)
    outer_local, inner_goal = intro_context(closure, g)
    newest = -len(g)
    need(inner_goal == delta(newest, H))
    inner_local, identity_goal = intro_context(inner_goal, outer_local)
    if len(identity_goal) == 2 and identity_goal[0] == identity_goal[1]:
        identity = refl(identity_goal[0])
    else:
        need(inner_local[-1][1] == identity_goal)
        identity = use(len(outer_local))
    major = [closure[0], [inner_goal[0], identity]]
    need(prove(major, g) == closure)
    B = sub(closure[0], newest, 1)
    local = g + [(sub(B, 0), B)]
    base = truth(local[-1][0], local)
    branch = use(len(g), S(s), base)
    p = [[], major, branch]
    need(prove(p, g) == delta(s, H))
    return p


def arbitrary_intro(B0, t, step_builder, g=INITIAL):
    """Recover Intro at t using Delta; step_builder rebuilds in exact scopes.

    step_builder(local, goal) must derive the displayed successor goal from
    the last clause, which is the appropriate base/progress assumption.
    """
    goal = [B0]
    H = [sub(B0, V, 1)]  # q_y B(V,y), its existential slot unused.

    def h_proof(context):
        Ht = at(H, V, t)
        local, successor_goal = intro_context(Ht, context)
        p = [Ht[0], step_builder(local, successor_goal)]
        need(prove(p, context) == Ht)
        return p

    transfer = delta_proof(t, H, g)
    delta_goal = prove(transfer, g)
    b = -len(g)
    clause_body = sub(delta_goal[0], b, 1)
    opened = g + [(sub(clause_body, 0), clause_body)]
    local, successor_goal = intro_context(goal, opened)
    z = -len(opened)
    hb = use(len(g), ONE, h_proof(local))
    hb_goal = prove(hb, local)
    c = -len(local)
    hb_body = sub(hb_goal[0], c, 1)
    hb_opened = local + [(sub(hb_body, 0), hb_body)]
    base = hb_opened[-1][0]
    if len(base) == 2 and base[0] == base[1]:
        base_proof = refl(base[0])
    else:
        need(base == local[-1][1])
        base_proof = use(len(opened))
    output = use(len(local), S(z), base_proof)
    step = [[], hb, output]
    need(prove(step, local) == successor_goal)
    introduced = [B0, step]
    need(prove(introduced, opened) == goal)
    p = [[], transfer, introduced]
    need(prove(p, g) == goal)
    return p


def reflexive_tower(local, goal):
    if len(goal) == 2:
        need(goal[0] == goal[1])
        return refl(goal[0])
    nested, target = intro_context(goal, local)
    return [goal[0], reflexive_tower(nested, target)]


def numerical_cases(template, name, target, zero_builder, successor_builder, g):
    """Case split with persistent builders; no target-proof weakening."""
    closure = D(template, U, name)
    local, goal = intro_context(closure, g)
    major = [closure[0], successor_builder(local, -len(g))]
    need(prove(major, g) == closure)
    B = sub(closure[0], -len(g), 1)
    opened = g + [(sub(B, 0), B)]
    result = [[], major, use(len(g), target, zero_builder(opened))]
    need(prove(result, g) == at(template, name, target))
    return result


def transport(equality_builder, equation_builder, template, name, g=INITIAL):
    """Derive h(t)=r from s=t and h(s)=r using inferred Export."""
    source, target = prove(equality_builder(g), g)
    left, right = prove(equation_builder(g), g)
    need(left == at(template, name, source))
    hx = at(template, name, X)
    packet = D(gate(Y, [C(P(Y), X, hx), C(P(Y), target, right)]))

    def successor(local, goal):
        z = 1 - len(local)
        step_template = [C(W, source, left), C(W, target, right)]
        result = numerical_cases(step_template, W, z, equality_builder,
                                 lambda enlarged, fresh: equation_builder(enlarged), local)
        need(prove(result, local) == goal)
        return result

    major = arbitrary_intro(packet[0], source, successor, g)
    branch = use(len(g), TWO, refl(0))
    result = [[], major, branch]
    need(prove(result, g) == [at(template, name, target), right])
    return result


def implication_formula(antecedent, consequent):
    return D(select(Y, antecedent, consequent), U, Y)


def implication(antecedent, consequent, builder, g=INITIAL):
    goal = implication_formula(antecedent, consequent)
    local, target = intro_context(goal, g)

    def hypothesis(enlarged):
        return refl(0) if antecedent == [0, 0] else use(len(g))

    branch = builder(local, hypothesis)
    need(prove(branch, local) == target)
    result = [goal[0], branch]
    need(prove(result, g) == goal)
    return result


def all_formula(template, name):
    return D(gate(W, at(template, name, P(W))), U, W)


def all_intro(template, name, successor_builder, g=INITIAL):
    goal = all_formula(template, name)
    local, target = intro_context(goal, g)
    branch = successor_builder(local, -len(g))
    need(prove(branch, local) == target)
    result = [goal[0], branch]
    need(prove(result, g) == goal)
    return result


def identity_iterator(n):
    # The ordinary zero-seeded identity iterator, compiled through R.
    return P([n, 0, S(P(1))])
