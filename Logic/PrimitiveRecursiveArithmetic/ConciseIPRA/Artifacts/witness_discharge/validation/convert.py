"""Untrusted exact-goal translations between four-rule and selected syntax."""
from reference_kernel import derive, opening, check as replay


def to_selected(p, context=None, scope=0, unconditional=None):
    context = [] if context is None else context
    unconditional = [] if unconditional is None else unconditional
    tag = p[0]
    if tag == 'r':
        return ['u', 0, p[1], []]
    if tag == 'u':
        j, t, premise = p[1:]
        return ['u', j + 1, t, [] if unconditional[j] else
                to_selected(premise, context, scope, unconditional)]
    if tag == 'i':
        goal, witness, branch = p[1:]
        body = opening(goal[0], witness, 1)
        fresh = -scope - 1
        eta = fresh if len(body) == 2 and witness == 0 else 0
        local = opening(body, eta)
        return ['i', witness, to_selected(branch, context + [([0, 0], local)],
                                          scope + 1, unconditional + [True])]
    if tag == 'e':
        goal, major, equality, branch = p[1:]
        paired = derive(major, context, scope)
        body = opening(paired[0], -scope - 1, 1)
        extended = context + [(opening(body, 0), body)]
        equation = derive(equality, extended, scope + 1)
        formula = derive(branch, extended, scope + 1)
        return ['e', paired[0], formula, equation[1],
                to_selected(major, context, scope, unconditional),
                to_selected(equality, extended, scope + 1, unconditional + [False]),
                to_selected(branch, extended, scope + 1, unconditional + [False])]
    raise ValueError('forward instruction')


def from_selected(goal, p, context=None, scope=0):
    # context here is the selected context, including the initial Refl clause.
    context = [([], [1, 1])] if context is None else context
    tag = p[0]
    if tag == 'u':
        index, target, premise = p[1:]
        if index == 0:
            return ['r', target]
        base, body = context[index]
        return ['u', index - 1, target,
                from_selected(base, premise, context, scope) if base else ['r', 0]]
    if tag == 'i':
        witness, branch = p[1:]
        body = opening(goal[0], witness, 1)
        fresh = -scope - 1
        eta = fresh if len(body) == 2 and witness == 0 else 0
        local = opening(body, eta)
        expected = opening(body, [0, fresh])
        return ['i', goal, witness,
                from_selected(expected, branch, context + [([], local)], scope + 1)]
    if tag == 'e':
        matrix, formula, target, major, equation, branch = p[1:]
        fresh = -scope - 1
        body = opening(matrix, fresh, 1)
        extended = context + [(opening(body, 0), body)]
        return ['e', goal,
                from_selected([matrix], major, context, scope),
                from_selected([fresh, target], equation, extended, scope + 1),
                from_selected(formula, branch, extended, scope + 1)]
    raise ValueError('selected instruction')


def certificate_to_selected(data):
    replay(data)
    return {'goal': data['goal'], 'proof': to_selected(data['proof'])}


def certificate_from_selected(data):
    result = {'goal': data['goal'], 'proof': from_selected(data['goal'], data['proof'])}
    replay(result)
    return result
