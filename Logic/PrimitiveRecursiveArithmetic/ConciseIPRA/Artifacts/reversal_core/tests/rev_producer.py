"""Untrusted named proof producer for the uniform root-reversal calculus.

It reuses the attributed upstream named AST, capture-free substitution and
serializer, but constructs the new equality proof explicitly. Neither
checker imports this file. Run test_rev.py to serialize and check fixtures.
"""
import copy
import itertools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / 'upstream'))
import native_producer as p

serial = itertools.count()


def fresh(prefix='rv'):
    return f'{prefix}_{next(serial)}'


def rho(formula):
    return p.Eq(formula[2], formula[1]) if formula[0] == 'eq' else formula


def box(term):
    return p.I(0, term, fresh('box_state'), 0)


def zero_anchor():
    # Unlike J(0), this equation has a direct packet even in the inherited
    # truthy-initializer arithmetic protocol. It prevents a normalization
    # cycle when the J(0)=0 computation itself is expanded below.
    return p.compute(p.I(p.TWO, p.ONE, fresh('anchor_state'), 0))


def xrule(major, variable, motive, minor):
    if major['goal'][0] != 'eq' or major['goal'][1] == 0:
        raise ValueError('X requires a syntactically nonzero equation source')
    _, source, target = major['goal']
    if minor['goal'] != p.substitute(motive, variable, source):
        raise ValueError('X minor does not match the source instance')
    return p.node('X', rho(p.substitute(motive, variable, target)),
                  major=major, variable=variable, motive=motive, minor=minor)


def qxrule(major, target, minor):
    _, variable, body = major['goal']
    if major['goal'][0] != 'q' or minor['goal'] != p.substitute(body, variable, 0):
        raise ValueError('QX premise mismatch')
    return p.node('QX', rho(p.substitute(body, variable, target)),
                  major=major, target=target, minor=minor)


def reverse(proof):
    if rho(proof['goal']) == proof['goal']:
        return proof
    return xrule(zero_anchor(), fresh('constant'), proof['goal'], proof)


def reflexivity(term):
    axiom = p.compute(box(term))
    hole = fresh('refl')
    return xrule(axiom, hole, p.Eq(p.V(hole), term), axiom)


def safe_transport(major, variable, motive, minor):
    return reverse(xrule(major, variable, motive, minor))


def join_zero(first, second):
    if first['goal'][2] != 0 or second['goal'][2] != 0:
        raise ValueError('join_zero requires two right-zero equations')
    left, right = first['goal'][1], second['goal'][1]
    if left == 0 or right == 0:
        raise ValueError('join_zero requires nonliteral-zero sources')
    state = fresh('common_box_state')
    def j(term):
        return p.I(0, term, state, 0)
    def to_box(proof):
        term = proof['goal'][1]
        hole = fresh('to_box')
        return xrule(proof, hole, p.Eq(j(p.V(hole)), term), p.compute(j(term)))
    first_box, second_box = to_box(first), to_box(second)
    hole = fresh('through_box')
    return safe_transport(reverse(second_box), hole,
                          p.Eq(left, p.V(hole)), first_box)


def transitivity(first, second):
    left, middle = first['goal'][1:]
    if second['goal'][1] != middle:
        raise ValueError('Transitivity endpoints differ')
    target = second['goal'][2]
    if middle != 0:
        hole = fresh('trans')
        return safe_transport(second, hole, p.Eq(left, p.V(hole)), first)
    if left == 0:
        return second
    if target == 0:
        return first
    return join_zero(first, reverse(second))


def congruence(major, transform):
    source, target = major['goal'][1:]
    if source != 0:
        hole = fresh('cong')
        return safe_transport(major, hole,
                              p.Eq(transform(source), transform(p.V(hole))),
                              reflexivity(transform(source)))
    if target == 0:
        return reflexivity(transform(0))
    return reverse(congruence(reverse(major), transform))


def transport(major, variable, motive, minor):
    source, target = major['goal'][1:]
    if minor['goal'] != p.substitute(motive, variable, source):
        raise ValueError('Transport premise mismatch')
    if source != 0:
        return safe_transport(major, variable, motive, minor)
    if motive[0] != 'eq':
        raise ValueError('This fixture producer only expands zero-source equation templates')
    left = lambda term: p.substitute(motive[1], variable, term)
    right = lambda term: p.substitute(motive[2], variable, term)
    return transitivity(transitivity(reverse(congruence(major, left)), minor),
                        congruence(major, right))


def specialize(major, target, minor):
    return reverse(qxrule(major, target, minor))


def convert(proof):
    """Translate the old named fixture tree to explicit REV rule trees."""
    rule = proof['rule']
    if rule == 'Tr':
        return transport(convert(proof['major']), proof['variable'],
                         proof['motive'], convert(proof['minor']))
    if rule == 'QE':
        return specialize(convert(proof['major']), proof['target'],
                          convert(proof['minor']))
    result = dict(proof)
    for key in ('major', 'minor', 'premise', 'continuation'):
        if key in proof:
            result[key] = convert(proof[key])
    return result


def normalize(proof):
    # The inherited packet format cannot directly compute with zero seed or
    # predecessor. Expand precisely those computation leaves, translate the
    # resulting ordinary transport, and recurse through the resulting tree.
    if proof['rule'] == 'Computation':
        expanded = p.expand_computation(proof)
        if expanded is not proof:
            return normalize(convert(expanded))
        return proof
    result = dict(proof)
    for key in ('major', 'minor', 'premise', 'continuation'):
        if key in proof:
            result[key] = normalize(proof[key])
    return result


class Emitter(p.Emitter):
    def emit(self, proof, context):
        if proof['rule'] not in ('X', 'QX'):
            return super().emit(proof, context)
        goal = self.formula(proof['goal'])
        if goal in context:
            self.trace.append({'rule': 'Hyp', 'goal': goal,
                               'floor': self.floor, 'instruction': None})
            return
        position = len(self.instructions)
        self.trace.append({'rule': proof['rule'], 'goal': goal,
                           'floor': self.floor, 'instruction': position})
        major = self.formula(proof['major']['goal'])
        if proof['rule'] == 'X':
            source, target = proof['major']['goal'][1:]
            packet = [major, self.term(source), self.term(target),
                      self.formula(proof['motive'], hole=proof['variable'])]
        else:
            packet = [major, 0, self.term(proof['target']), major[0]]
        self.instructions.append(packet)
        saved_floor = self.floor
        self.emit(proof['major'], context)
        self.floor = saved_floor
        self.allocate()
        self.emit(proof['minor'], context + [[]])

    def packet(self, proof):
        proof = normalize(proof)
        goal = self.formula(proof['goal'])
        self.emit(proof, [])
        packet = list(reversed(self.instructions)) + [goal]
        for event in self.trace:
            if event['instruction'] is not None:
                event['packet_index'] = len(self.instructions) - 1 - event['instruction']
        return packet


def conditional_zero_symmetry():
    """A closed implication encoding with the essential assumption 0=1."""
    index, eigen, unused = fresh('sym_y'), fresh('sym_z'), fresh('unused')
    left = lambda n: p.C(n, 0, p.ONE)
    right = lambda n: p.C(n, p.ONE, 0)
    body = p.Eq(left(p.V(index)), right(p.V(index)))
    assumption = p.hyp(p.Eq(left(0), right(0)))
    hole = fresh('extract_l')
    first = transport(p.compute(left(0)), hole,
                      p.Eq(p.V(hole), right(0)), assumption)
    hole = fresh('extract_r')
    zero_one = transport(p.compute(right(0)), hole, p.Eq(0, p.V(hole)), first)
    one_zero = reverse(zero_one)
    successor = p.S(p.V(eigen))
    step = transitivity(transitivity(p.compute(left(successor)), one_zero),
                        reverse(p.compute(right(successor))))
    return p.introduction(p.D(unused, index, body), 0, eigen, 'case', step)


def fixtures():
    cases = []
    def add(name, proof, meaning, accept=True, allow_forbidden=False):
        emitter = Emitter(allow_forbidden)
        packet = emitter.packet(proof)
        cases.append({'name': name, 'meaning': meaning, 'accept': accept,
                      'packet': packet, 'trace': emitter.trace,
                      'goal_kind': proof['goal'][0]})
        return cases[-1]
    add('new_reflexivity_zero', reflexivity(0),
        'The new one-X reflexivity derivation, including certified-zero computation normalization.')
    add('new_reflexivity_two', reflexivity(p.TWO),
        'The computation axiom is used twice as the two premises of one X rule.')
    nested = p.I(p.TWO, p.ONE, 'nested_u', p.I(p.V('nested_u'), 0, 'nested_v', p.S(p.V('nested_v'))))
    add('new_reflexivity_nested', reflexivity(nested),
        'Reflexivity for a term with a genuinely nested iterator body.')
    anchor = zero_anchor()
    add('root_reversal_zero_source', reverse(anchor),
        'A constant template reverses an equation with nonzero left side into a literal-zero-source equation.')
    add('conditional_zero_symmetry', conditional_zero_symmetry(),
        'Inside a case-DI assumption, extracts 0=1 and derives 1=0 by root reversal; no induction is used.')
    first = p.compute(box(0))
    add('new_zero_join', join_zero(first, zero_anchor()),
        'The new common-box proof joins two nonliteral terms both provably zero.')
    zero_major = reverse(first)
    transform = lambda value: p.I(p.ONE, 0, 'cong_u',
                                    p.I(value, p.V('cong_u'), 'cong_v', p.S(p.V('cong_v'))))
    add('zero_source_nested_congruence', congruence(zero_major, transform),
        'Full congruence at a literal-zero major source through nested iterator binders.')
    hole = fresh('zero_transport')
    motive = p.Eq(p.C(p.V(hole), 0, p.ONE), p.C(p.V(hole), 0, p.ONE))
    add('unrestricted_equation_transport',
        transport(zero_major, hole, motive, reflexivity(p.C(0, 0, p.ONE))),
        'The derived full equation-transport chain at a literal-zero source.')
    add('atomic_progress_Q_closure', convert(p.identity_closure('rv_id')),
        'Witnessed equation progress plus DE obtains Q; the step uses the actual induction hypothesis.')
    major = p.identity_closure('rv_spec')
    _, y, body = major['goal']
    add('QX_arbitrary_target', convert(p.specialize(
        major, p.S(nested), p.computation(p.substitute(body, y, 0)))),
        'QX specialization at a compound term, followed by root reversal of its atomic result.')
    add('compound_cases_nested_Q', convert(p.nested_identity_closure()),
        'Case DI above Q, with an outer numerical parameter retained through nested induction.')
    add('nonvacuous_D_elimination', convert(p.nonvacuous_elimination()),
        'An existential witness is opened, used in QX, and discharged without escaping.')
    add('contextual_atomic_induction', convert(p.contextual_seed_congruence()),
        'Equation induction with an essential retained equality assumption and a genuine induction hypothesis.')
    term = p.I(0, p.ONE, 'tr_q_state', 0)
    original = p.identity_closure('tr_q', term)
    hole = 'tr_q_hole'
    motive = p.Q('tr_q_y', p.Eq(p.I(p.V('tr_q_y'), p.V(hole), 'tr_q_u', p.V('tr_q_u')), p.V(hole)))
    add('transport_under_Q', convert(p.transport(p.compute(term), hole, motive, original)),
        'General-template X on a Q formula; rho leaves its outer constructor unchanged.')
    d_source = p.nonvacuous_elimination()
    # A constant D template exercises general-template X without relying on
    # syntactic term occurrence or a hidden equation-only restriction.
    add('transport_under_D', safe_transport(zero_anchor(), fresh('const_D'),
                                          d_source['goal'], convert(d_source)),
        'General-template X on a D formula with a constant template.')
    add('forbidden_compound_progress', convert(p.forbidden_compound_progress()),
        'A forged compound progress step is rejected: the checker supplies the zero case, not an induction hypothesis.',
        accept=False, allow_forbidden=True)
    return cases


def zero_neutral(packet):
    result = copy.deepcopy(packet)
    for command in result[:-1]:
        if isinstance(command, list) and len(command) == 4 and command[0] == []:
            command[0] = 0
    return result
