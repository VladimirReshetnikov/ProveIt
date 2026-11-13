"""Untrusted certificate compilers for the matched newest-use calculi.

The proof checker does not import this file.  Each produced certificate is
rechecked independently by the complete command-line checker.
"""
from copy import deepcopy


def map_syntax(a, f, depth=0):
    if type(a) is int:
        return f(a, depth)
    size = len(a)
    return [map_syntax(b, f, depth + (2 if size == 1 else
            int(size == 3 and i == 2))) for i, b in enumerate(a)]


def lift(a, amount):
    return map_syntax(a, lambda i, d: i + amount if i > d else i)


def raw_open(a, t, depth=0):
    return map_syntax(a, lambda i, d: lift(t, d) if i == d + 1 else
                      i - (i > d + 1), depth)


def normal(a):
    if type(a) is int:
        return a
    a = [normal(b) for b in a]
    if len(a) == 3:
        c, seed, body = a
        if c == 0:
            return seed
        if type(c) is list and len(c) == 2:
            return normal(raw_open(body, normal([c[1], seed, body])))
    return a


def opening(a, t, depth=0):
    return normal(raw_open(a, t, depth))


def rename(a, rho):
    return map_syntax(a, lambda i, d: rho.get(i, i) if i < 0 else i)


def name_matrix(t):
    # Under D: x has index 2 and y has index 1.  Under I's body x is 3.
    return [[1, 0, 3], [1, 0, deepcopy(t)]]


def to_newest(goal, proof, source=None, target=None, rho=None, indexes=None):
    """Translate under an injective scope renaming and context embedding.

    A Use node regenerates its antecedent proof below a newly opened name.
    It never weakens an already generated target proof tree.
    """
    source = [] if source is None else source
    target = [] if target is None else target
    rho = {} if rho is None else rho
    indexes = list(range(len(source))) if indexes is None else indexes
    tag = proof[0]
    if tag == 'r':
        return ['r']
    old_fresh, new_fresh = -len(source) - 1, -len(target) - 1
    if tag == 'u':
        j, t, premise = proof[1:]
        t = rename(t, rho)
        matrix = name_matrix(t)
        body = opening(matrix, new_fresh, 1)
        clause = (opening(body, 0), body)
        base, old_body = source[j]
        branch_goal = opening(rename(old_body, rho), new_fresh)
        branch_premise = to_newest(base, premise, source, target + [clause],
                                   rho, indexes) if base else []
        return ['e', matrix, branch_goal, ['i', t, ['r']],
                ['u', indexes[j], branch_premise]]
    extended_rho = dict(rho)
    extended_rho[old_fresh] = new_fresh
    extended_indexes = indexes + [len(target)]
    if tag == 'i':
        t, branch = proof[1:]
        old_body = opening(goal[0], t, 1)
        old_eta = old_fresh if len(old_body) == 2 and t == 0 else 0
        old_clause = ([], opening(old_body, old_eta))
        new_goal, new_t = rename(goal, rho), rename(t, rho)
        new_body = opening(new_goal[0], new_t, 1)
        new_eta = new_fresh if len(new_body) == 2 and new_t == 0 else 0
        new_clause = ([], opening(new_body, new_eta))
        branch_goal = opening(old_body, [0, old_fresh])
        return ['i', new_t, to_newest(branch_goal, branch,
                source + [old_clause], target + [new_clause],
                extended_rho, extended_indexes)]
    if tag == 'e':
        matrix, formula, major, branch = proof[1:]
        old_body = opening(matrix, old_fresh, 1)
        old_clause = (opening(old_body, 0), old_body)
        new_matrix = rename(matrix, rho)
        new_body = opening(new_matrix, new_fresh, 1)
        new_clause = (opening(new_body, 0), new_body)
        return ['e', new_matrix, rename(formula, extended_rho),
                to_newest([matrix], major, source, target, rho, indexes),
                to_newest(formula, branch, source + [old_clause],
                          target + [new_clause], extended_rho, extended_indexes)]
    raise ValueError('reference proof tag')


def to_reference(goal, proof, context=None):
    """The reverse inclusion merely supplies the inferred Use target."""
    context = [] if context is None else context
    tag = proof[0]
    if tag == 'r':
        return ['r']
    if tag == 'u':
        j, premise = proof[1:]
        base, body = context[j]
        return ['u', j, -len(context),
                to_reference(base, premise, context) if base else []]
    fresh = -len(context) - 1
    if tag == 'i':
        t, branch = proof[1:]
        body = opening(goal[0], t, 1)
        hyp = opening(body, fresh if len(body) == 2 and t == 0 else 0)
        return ['i', t, to_reference(opening(body, [0, fresh]), branch,
                                     context + [([], hyp)])]
    if tag == 'e':
        matrix, formula, major, branch = proof[1:]
        body = opening(matrix, fresh, 1)
        return ['e', matrix, formula,
                to_reference([matrix], major, context),
                to_reference(formula, branch,
                             context + [(opening(body, 0), body)])]
    raise ValueError('newest proof tag')


def from_upstream(proof):
    """Replace the upstream global reflexivity clause by primitive Refl.

    Dropping context entry 0 leaves fresh levels unchanged, because our
    checkers use fresh=-len(context)-1 instead of -len(context).
    """
    if not proof:
        return []
    tag = proof[0]
    if tag == 'u':
        j, t, premise = proof[1:]
        return ['r'] if j == 0 else ['u', j - 1, deepcopy(t),
                                     from_upstream(premise)]
    if tag == 'i':
        return ['i', deepcopy(proof[1]), from_upstream(proof[2])]
    if tag == 'e':
        return ['e', deepcopy(proof[1]), deepcopy(proof[2]),
                from_upstream(proof[3]), from_upstream(proof[4])]
    raise ValueError('upstream proof tag')
