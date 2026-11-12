"""Untrusted proof builders for initializer evaluation and its two controls.

The three standalone checkers never import this module. An arithmetic proof
is a tuple (left_endpoint, right_endpoint, certificate_tree). Positive
fixtures are adapted from the pinned uniform_step verification producer.
"""

ZERO = 0
ONE = ['s', 0]


def iterator(counter, seed, body):
    return seed if counter == 0 else ['i', counter, seed, body]


def opening(a, value, depth=0):
    if type(a) is int:
        if a <= depth:
            return a
        return value if a == depth + 1 else a - 1
    if a[0] == 's':
        return ['s', opening(a[1], value, depth)]
    if a[0] == 'i':
        return iterator(opening(a[1], value, depth),
                        opening(a[2], value, depth),
                        opening(a[3], value, depth + 1))
    if a[0] == '=':
        return ['=', opening(a[1], value, depth), opening(a[2], value, depth)]
    if a[0] == 'd':
        return ['d', opening(a[1], value, depth + 2)]
    raise ValueError(a)


class Builder:
    def __init__(self, mode):
        if mode not in ('seed', 'step', 'control'):
            raise ValueError(mode)
        self.mode = mode

    def refl(self, a):
        if self.mode != 'control':
            return a, a, ['r', a]
        equation = self.comp(0, a, 1)
        return self.transport(equation, equation, 1)

    def primitive(self, p, q):
        _, counter, seed, body = q[0]
        if counter[0] != 's':
            raise ValueError('A successor counter is required')
        n = counter[1]
        expected = seed if self.mode == 'seed' else iterator(n, seed, body)
        if p[0] != expected:
            raise ValueError('Incorrect arithmetic major source')
        state = iterator(n, p[1], body) if self.mode == 'seed' else p[1]
        return q[1], opening(body, state), ['x', p[2], q[2]]

    def comp(self, counter, seed, body):
        lhs = iterator(['s', counter], seed, body)
        rhs = opening(body, iterator(counter, seed, body))
        if self.mode == 'control':
            return lhs, rhs, ['r', counter, seed, body]
        major = seed if self.mode == 'seed' else iterator(counter, seed, body)
        return self.primitive(self.refl(major), self.refl(lhs))

    def pivot(self, p, q):
        if p[0] != q[0]:
            raise ValueError('Different pivot sources')
        if self.mode == 'control':
            return self.transport(p, q, 1)
        frame = iterator(ONE, p[0], 1)
        return self.primitive(p, self.primitive(q, self.refl(frame)))

    def sym(self, p):
        return self.pivot(self.refl(p[0]), p)

    def trans(self, p, q):
        if p[1] != q[0]:
            raise ValueError('Different transitivity endpoints')
        return self.pivot(q, self.sym(p))

    def transport(self, p, q, template):
        if q[0] != opening(template, p[0]):
            raise ValueError('Different transport endpoints')
        if self.mode == 'control':
            return q[1], opening(template, p[1]), ['x', template, p[2], q[2]]
        return self.pivot(self.cong(p, template), q)

    def cong(self, p, template):
        if self.mode == 'control':
            return self.transport(p, self.refl(opening(template, p[0])), template)
        frame = iterator(ONE, p[0], template)
        first = self.primitive(self.refl(p[0]), self.refl(frame))
        return self.primitive(p, first)

    def step(self, p, q):
        _, counter, seed, body = q[0]
        if p[0] != iterator(counter[1], seed, body):
            raise ValueError('Different predecessor states')
        if self.mode == 'step' or self.mode == 'seed' and counter[1] == 0:
            return self.primitive(p, q)
        computation = self.comp(counter[1], seed, body)
        bridge = self.pivot(q, computation)
        return self.transport(p, bridge, body)

    def seed(self, p, q):
        _, counter, seed, body = q[0]
        if p[0] != seed:
            raise ValueError('Different initializer sources')
        if self.mode == 'seed' or self.mode == 'step' and counter[1] == 0:
            return self.primitive(p, q)
        template = iterator(counter[1], 1, body)
        states = self.cong(p, template)
        return self.step(states, q)

    def use_equation(self, index, witness, premise, lhs, rhs):
        return lhs, rhs, ['u', index, witness, premise[2]]


def fixture(p):
    return {'goal': ['=', p[0], p[1]], 'proof': p[2]}


def positive_fixtures(mode):
    b = Builder(mode)
    cases = {}
    terms = [0, ONE, ['s', ONE], iterator(ONE, 0, ['s', 1]),
             iterator(ONE, ONE, iterator(1, ONE, ['s', 1]))]
    for i, a in enumerate(terms):
        cases[f'reflexivity_{i}'] = fixture(b.refl(a))
    for n_id, n in enumerate([0, ONE, ['s', ONE]]):
        for h_id, h in enumerate([1, 0, ['s', 1], iterator(ONE, 1, ['s', 1]),
                                 iterator(1, ONE, 1), iterator(iterator(1, 0, 1), ONE, 1)]):
            p = b.comp(n, ONE, h)
            cases[f'computation_{n_id}_{h_id}'] = fixture(p)
            cases[f'symmetry_{n_id}_{h_id}'] = fixture(b.sym(p))
            cases[f'resolution_{n_id}_{h_id}'] = fixture(b.pivot(p, p))
            template = iterator(1, ONE, ['s', 1])
            cases[f'transport_{n_id}_{h_id}'] = fixture(
                b.transport(p, b.refl(opening(template, p[0])), template))
    matrix = ['=', 1, 1]
    goal = ['d', matrix]
    proof = ['i', goal, 0, b.refl(['s', -1])[2]]
    cases['d_progress'] = {'goal': goal, 'proof': proof}
    cases['d_case'] = {'goal': goal, 'proof': ['i', goal, ONE, b.refl(['s', -1])[2]]}
    cases['d_elimination_used_clause'] = {
        'goal': ['=', ONE, ONE],
        'proof': ['e', ['=', ONE, ONE], proof, ['u', 0, ONE, b.refl(0)[2]]],
    }
    nested = ['d', goal]
    cases['nested_d_used_assumption'] = {
        'goal': nested,
        'proof': ['i', nested, 0, ['u', 0, 0, b.refl(0)[2]]],
    }
    matrix = ['=', iterator(1, ONE, 1), ONE]
    goal = ['d', matrix]
    old = b.use_equation(0, 0, b.refl(0), iterator(-1, ONE, 1), ONE)
    next_equation = b.trans(b.comp(-1, ONE, 1), old)
    inductive = ['i', goal, 0, next_equation[2]]
    cases['induction_uses_hypothesis'] = {'goal': goal, 'proof': inductive}
    result = ['=', iterator(terms[-1], ONE, 1), ONE]
    cases['induction_instantiated_nested_counter'] = {
        'goal': result,
        'proof': ['e', result, inductive, ['u', 0, terms[-1], b.refl(ONE)[2]]],
    }
    return cases
