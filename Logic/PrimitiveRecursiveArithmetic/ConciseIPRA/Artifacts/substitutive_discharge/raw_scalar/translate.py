"""Untrusted exact-goal translations, checked by both endpoint verifiers."""
from pathlib import Path
import importlib.util

import checker
import control_separate as control
from proofs import H0, truth, transport, reflexivity, ordinary_elimination


def to_control(p):
    tag, *a = p
    if tag == 'c':
        return p
    if tag == 'u':
        j, t, branch = a
        return [tag, j, t, to_control(branch)]
    if tag == 'i':
        goal, t, branch = a
        return [tag, goal, t, to_control(branch)]
    if tag == 'e':
        goal, template, major, equality, branch = a
        return [tag, goal, to_control(major),
                ['t', template, to_control(equality), to_control(branch)]]
    raise ValueError('unknown instruction')


def from_control(p, g=None, n=0):
    if g is None:
        g = []
    tag, *a = p
    if tag == 'c':
        return p
    if tag == 'u':
        j, t, branch = a
        return [tag, j, t, from_control(branch, g, n)]
    if tag == 'i':
        goal, t, branch = a
        body = checker.opening(goal[0], t, 1)
        start = -n - 1 if len(body) == 2 and t == 0 else 0
        hyp = checker.opening(body, start)
        return [tag, goal, t, from_control(branch, g + [(H0, hyp)], n + 1)]
    if tag == 'e':
        goal, major, branch = a
        paired = control.derive(major, g, n)
        body = checker.opening(paired[0], -n - 1, 1)
        local = g + [(checker.opening(body, 0), body)]
        return ordinary_elimination(goal, from_control(major, g, n),
                                    from_control(branch, local, n + 1))
    if tag == 't':
        template, equality, branch = a
        _, target = control.derive(equality, g, n)
        return transport(template, target, from_control(equality, g, n),
                         from_control(branch, g, n), n, len(g))
    raise ValueError('unknown instruction')


def checked_round_trip(data):
    checker.check(data)
    c = {'goal': data['goal'], 'proof': to_control(data['proof'])}
    control.check(c)
    back = {'goal': data['goal'], 'proof': from_control(c['proof'])}
    checker.check(back)
    return c, back


def load_ce5(path):
    spec = importlib.util.spec_from_file_location('reference_ce5', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def from_ce5(p, old, context=None, n=0):
    """Translate the repository CE5 rule set. Context records old/new bases."""
    if context is None:
        context = []
    old_g = [(o, b) for o, _, b in context]
    tag, *a = p
    if tag == 'r':
        return reflexivity(a[0], n, len(context))
    if tag == 'u':
        j, t, premise = a
        old_base, new_base, _ = context[j]
        new_premise = (truth() if old_base != new_base
                       else from_ce5(premise, old, context, n))
        return [tag, j, t, new_premise]
    if tag == 'v':
        major, minor = a
        s, t = old.derive(major, old_g, n)
        b, r = old.derive(minor, old_g, n)
        eq = from_ce5(major, old, context, n)
        mi = from_ce5(minor, old, context, n)
        if b == s:
            return transport([1, t], r, mi, eq, n, len(context))
        c, seed, h = b
        if c == 0:
            bt = transport([b, 1], t, eq, ['c', b], n, len(context))
            target = t
        else:
            bt = transport([b, h], t, eq, ['c', b], n, len(context))
            target = checker.opening(h, t)
        return transport([1, target], r, mi, bt, n, len(context))
    if tag == 'i':
        goal, t, branch = a
        body = checker.opening(goal[0], t, 1)
        eta = -n - 1 if len(body) == 2 and t == 0 else 0
        hyp = checker.opening(body, eta)
        return [tag, goal, t, from_ce5(branch, old, context + [([0, 0], H0, hyp)], n + 1)]
    if tag == 'e':
        goal, major, branch = a
        paired = old.derive(major, old_g, n)
        body = checker.opening(paired[0], -n - 1, 1)
        base = checker.opening(body, 0)
        return ordinary_elimination(goal, from_ce5(major, old, context, n),
                                    from_ce5(branch, old, context + [(base, base, body)], n + 1))
    raise ValueError('unknown CE5 instruction')


def ce5_fixtures():
    z, one, step = -1, [0, 0], [0, 1]
    matrix = [[1, 0, step], 1]
    goal = [matrix]
    identity = ['i', goal, 0, ['v', ['u', 0, 0, ['r', 0]], ['r', [[0, z], 0, step]]]]
    zero = [0, 0, step]
    zero_calc = ['v', ['r', 0], ['r', zero]]
    succ = [one, 0, step]
    succ_calc = ['v', ['r', zero], ['r', succ]]
    return [
        {'goal': [0, 0], 'proof': ['r', 0]},
        {'goal': [zero, 0], 'proof': zero_calc},
        {'goal': [succ, [0, zero]], 'proof': succ_calc},
        {'goal': goal, 'proof': identity},
        {'goal': [succ, one],
         'proof': ['e', [succ, one], identity, ['u', 0, one, zero_calc]]},
    ]


def verify_ce5(path):
    old = load_ce5(path)
    count = 0
    for data in ce5_fixtures():
        old.verify(data)
        result = {'goal': data['goal'], 'proof': from_ce5(data['proof'], old)}
        checker.check(result)
        count += 1
    return count
