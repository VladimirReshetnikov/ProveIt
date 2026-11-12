"""Untrusted named-syntax producer of fully expanded native QE certificates.

This module is not imported by qe_restricted.py. It builds ordinary primitive
Choice-DI proof trees, then emits their complete JSON packets. Its named syntax
is solely a readable certificate-authoring aid; no macro is trusted by the
checker. No arithmetic evaluator is used to prove a goal.
"""
import copy
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def V(name):
    return ('v', name)


def S(term):
    return ('s', term)


def I(counter, initial, state, update):
    return ('i', counter, initial, state, update)


def Eq(left, right):
    return ('eq', left, right)


def Q(variable, body):
    return ('q', variable, body)


def D(witness, index, body):
    return ('d', witness, index, body)


def C(index, initial, positive):
    return I(index, initial, '_unused_state', positive)


ONE = S(0)
TWO = S(ONE)


def substitute(tree, variable, value):
    """Capture-free on the globally distinct named binders used here."""
    if tree == 0:
        return 0
    tag = tree[0]
    if tag == 'v':
        return value if tree[1] == variable else tree
    if tag == 's':
        return S(substitute(tree[1], variable, value))
    if tag == 'i':
        _, n, a, u, h = tree
        return I(substitute(n, variable, value), substitute(a, variable, value),
                 u, h if u == variable else substitute(h, variable, value))
    if tag == 'eq':
        return Eq(substitute(tree[1], variable, value),
                  substitute(tree[2], variable, value))
    if tag == 'q':
        _, y, body = tree
        return tree if y == variable else Q(y, substitute(body, variable, value))
    if tag == 'd':
        _, x, y, body = tree
        return tree if variable in (x, y) else D(x, y, substitute(body, variable, value))
    raise ValueError(tag)


def node(rule, goal, **fields):
    return {'rule': rule, 'goal': goal, **fields}


def hyp(goal):
    return node('Hyp', goal)


def computation(goal):
    return node('Computation', goal)


def transport(major, variable, motive, minor, role='transport'):
    assert major['goal'][0] == 'eq'
    _, s, t = major['goal']
    assert minor['goal'] == substitute(motive, variable, s)
    return node('Tr', substitute(motive, variable, t), major=major,
                variable=variable, motive=motive, minor=minor, role=role)


def specialize(major, target, minor, role='QE'):
    assert major['goal'][0] == 'q'
    _, y, body = major['goal']
    assert minor['goal'] == substitute(body, y, 0)
    return node('QE', substitute(body, y, target), major=major,
                target=target, minor=minor, role=role)


def introduction(goal, witness, eigen, mode, premise):
    _, x, y, body = goal
    opened = substitute(body, x, witness)
    assert premise['goal'] == substitute(opened, y, S(V(eigen)))
    return node('DI', goal, witness=witness, eigen=eigen, mode=mode,
                premise=premise)


def elimination(major, eigen, continuation):
    assert major['goal'][0] == 'd'
    return node('DE', continuation['goal'], major=major, eigen=eigen,
                continuation=continuation)


def identity_closure(prefix='id', initial=0):
    """Prove Q_y (I(y,initial;u.u)=initial) by literal-equation induction."""
    y, x, u = prefix + '_y', prefix + '_x', prefix + '_u'
    z, a, v = prefix + '_z', prefix + '_a', prefix + '_v'
    body = Eq(I(V(y), initial, u, V(u)), initial)
    current = I(V(z), initial, u, V(u))
    following = I(S(V(z)), initial, u, V(u))
    step = transport(hyp(Eq(current, initial)), v, Eq(following, V(v)),
                     computation(Eq(following, current)))
    paired = D(x, y, body)
    intro = introduction(paired, 0, z, 'progress', step)
    return elimination(intro, a, hyp(Q(y, body)))


def nested_identity_closure():
    """Prove Q_a Q_n (I(n,a;u.u)=a), preserving an outer parameter."""
    outer_y, outer_x, outer_z, outer_a = 'outer_y', 'outer_x', 'outer_z', 'outer_a'
    inner_y, inner_u = 'inner_y', 'inner_u'
    body = Q(inner_y, Eq(I(V(inner_y), V(outer_y), inner_u, V(inner_u)), V(outer_y)))
    paired = D(outer_x, outer_y, body)
    step = identity_closure('inner', initial=S(V(outer_z)))
    intro = introduction(paired, 0, outer_z, 'case', step)
    return elimination(intro, outer_a, hyp(Q(outer_y, body)))


def reconstruct_specialization(major, target, minor, prefix='pack'):
    """Expand the theorem's ten-node replacement into primitive rules."""
    _, original_y, original_body = major['goal']
    x, y = prefix + '_x', prefix + '_y'
    z, a = prefix + '_z', prefix + '_a'
    v, w = prefix + '_v', prefix + '_w'
    gate = Eq(C(V(y), target, V(x)), target)
    paired = D(x, y, gate)
    pack = introduction(paired, target, z, 'case',
                        computation(Eq(C(S(V(z)), target, target), target)))
    opened_gate = substitute(gate, x, V(a))
    gate_one = specialize(hyp(Q(y, opened_gate)), ONE,
                          computation(Eq(C(0, target, V(a)), target)),
                          role='calibration_at_one')
    equality = transport(computation(Eq(C(ONE, target, V(a)), V(a))),
                         v, Eq(V(v), target), gate_one,
                         role='extract_named_value')
    at_variable = specialize(major, V(a), minor,
                             role='reconstructed_variable_specialization')
    conclusion = transport(equality, w,
                           substitute(original_body, original_y, V(w)),
                           at_variable, role='substitute_named_value')
    return elimination(pack, a, conclusion)


class Emitter:
    """Untrusted serializer implementing the documented sorted tree encoding."""
    def __init__(self):
        self.floor = 0
        self.parameters = {}
        self.instructions = []
        self.trace = []

    def term(self, term, env=(), hole=None):
        if term == 0:
            return 0
        tag = term[0]
        if tag == 'v':
            name = term[1]
            if name in env:
                return 2 * env.index(name) + 1
            if name == hole:
                return 2 * len(env) + 1
            if name in self.parameters:
                return self.parameters[name]
            raise ValueError('Unscoped producer variable: ' + name)
        if tag == 's':
            return [self.term(term[1], ('_protected_zero',) + env, hole)]
        if tag == 'i':
            _, n, a, u, h = term
            padding = ('_protected_zero', '_protected_zero')
            return [self.term(n, padding + env, hole),
                    self.term(a, padding + env, hole),
                    self.term(h, (u, u) + env, hole)]
        raise ValueError('Not a numerical term: ' + repr(term))

    def formula(self, formula, env=(), hole=None):
        tag = formula[0]
        if tag == 'eq':
            return [self.term(formula[1], env, hole),
                    self.term(formula[2], env, hole)]
        if tag == 'q':
            return [self.formula(formula[2], (formula[1],) + env, hole)]
        if tag == 'd':
            _, x, y, body = formula
            return [0, 0, self.formula(body, (y, x) + env, hole)]
        raise ValueError('Not a formula: ' + repr(formula))

    def emit(self, proof, context):
        raw_goal = self.formula(proof['goal'])
        if raw_goal in context:
            self.trace.append({'rule': 'Hyp', 'goal': raw_goal,
                               'floor': self.floor, 'instruction': None})
            return
        rule = proof['rule']
        if rule == 'Hyp':
            raise ValueError('Producer hypothesis is absent: ' + repr(raw_goal))
        index = len(self.instructions)
        self.trace.append({'rule': rule, 'role': proof.get('role', rule),
                           'goal': raw_goal, 'floor': self.floor,
                           'instruction': index})
        if rule == 'Computation':
            self.instructions.append([0, 0])
        elif rule in ('Tr', 'QE'):
            major = self.formula(proof['major']['goal'])
            payload = (self.formula(proof['motive'], hole=proof['variable'])
                       if rule == 'Tr' else self.term(proof['target']))
            self.instructions.append([major, payload])
            self.emit(proof['major'], context)
            self.emit(proof['minor'], context)
        elif rule == 'DI':
            witness = self.term(proof['witness'])
            # In the inherited packet protocol, a DI witness must be truthy.
            # Numerical I(0,0;u.0) is a truthful zero encoding. Every occurrence
            # here using zero has an unused witness coordinate.
            if witness == 0:
                witness = [0, 0, 0]
            self.instructions.append([[] if proof['mode'] == 'case' else 0, witness])
            self.floor -= 1
            eigen = proof['eigen']
            assert eigen not in self.parameters
            self.parameters[eigen] = self.floor
            _, x, y, body = proof['goal']
            opened = substitute(body, x, proof['witness'])
            local = substitute(opened, y, V(eigen) if proof['mode'] == 'progress' else 0)
            self.emit(proof['premise'], context + [self.formula(local)])
            del self.parameters[eigen]
        elif rule == 'DE':
            self.instructions.append([self.formula(proof['major']['goal']), 0])
            self.emit(proof['major'], context)
            self.floor -= 1
            eigen = proof['eigen']
            assert eigen not in self.parameters
            self.parameters[eigen] = self.floor
            _, x, y, body = proof['major']['goal']
            opened = Q(y, substitute(body, x, V(eigen)))
            self.emit(proof['continuation'], context + [self.formula(opened)])
            del self.parameters[eigen]
        else:
            raise ValueError(rule)

    def packet(self, proof):
        goal = self.formula(proof['goal'])
        self.emit(proof, [])
        packet = list(reversed(self.instructions)) + [goal]
        for event in self.trace:
            if event['instruction'] is not None:
                event['packet_index'] = len(self.instructions) - 1 - event['instruction']
        return packet


def create_cases():
    cases = []
    for name, target in [('two', TWO),
                         ('nested_successor_iterator', S(I(TWO, 0, 'ramp_u', S(V('ramp_u'))))),
                         ('compound_formula', TWO)]:
        major = (nested_identity_closure() if name == 'compound_formula'
                 else identity_closure('original_' + name))
        _, y, body = major['goal']
        base = (identity_closure('inner') if name == 'compound_formula'
                else computation(substitute(body, y, 0)))
        expanded = reconstruct_specialization(major, target, base, 'pack_' + name)
        emitter = Emitter()
        packet = emitter.packet(expanded)
        record = {'name': 'expanded_QE_' + name, 'accept': True,
                  'closed': True, 'packet': packet, 'proof_tree': expanded,
                  'trace': emitter.trace,
                  'meaning': ('Closed conditional closure Q_n(I(n,t;u.u)=t), with transport beneath Q.'
                              if name == 'compound_formula' else
                              'Closed equation I(t,0;u.u)=0 obtained through the expanded V1 specialization theorem.')}
        cases.append(record)
        direct = specialize(major, target, base, role='forbidden_direct_target')
        direct_emitter = Emitter()
        cases.append({'name': 'reject_direct_QE_' + name, 'accept': False,
                      'baseline_accept': True, 'closed': True,
                      'packet': direct_emitter.packet(direct),
                      'proof_tree': direct, 'trace': direct_emitter.trace,
                      'meaning': 'Same closed conclusion, but direct non-variable/non-one QE is forbidden.'})
        variable_event = next(e for e in emitter.trace
                              if e.get('role') == 'reconstructed_variable_specialization')
        index = variable_event['packet_index']
        for suffix, replacement in [('wrong_allocated_variable', -1),
                                    ('unallocated_variable', -999),
                                    ('float_variable_alias', -2.0),
                                    ('numeric_positive_leaf', 1)]:
            mutated = copy.deepcopy(packet)
            mutated[index][1] = replacement
            cases.append({'name': 'reject_' + suffix + '_' + name,
                          'accept': False, 'closed': True, 'packet': mutated,
                          'meaning': 'A targeted scope/target mutation of the reconstructed variable QE.'})
        missing = copy.deepcopy(packet)
        computation_event = next(e for e in emitter.trace if e['rule'] == 'Computation')
        del missing[computation_event['packet_index']]
        cases.append({'name': 'reject_missing_computation_' + name,
                      'accept': False, 'closed': True, 'packet': missing,
                      'meaning': 'An essential primitive computation certificate was removed.'})
    one_major = identity_closure('direct_one')
    _, y, body = one_major['goal']
    one_proof = specialize(one_major, ONE, computation(substitute(body, y, 0)))
    one_emitter = Emitter()
    cases.append({'name': 'permitted_direct_QE_one', 'accept': True, 'closed': True,
                  'packet': one_emitter.packet(one_proof), 'proof_tree': one_proof,
                  'trace': one_emitter.trace})
    cases.extend([
        {'name': 'reject_canonical_false', 'accept': False, 'closed': True,
         'packet': [[0, 0], [0, [0]]]},
        {'name': 'reject_free_parameter_in_closed_goal', 'accept': False, 'closed': True,
         'packet': [[0, 0], [[0, -1, 0], -1]]},
        {'name': 'reject_malformed_arity_four', 'accept': False, 'closed': True,
         'packet': [[0, 0], [0, 0, 0, 0]]},
        {'name': 'primitive_zero_computation', 'accept': True, 'closed': True,
         'packet': [[0, 0], [[0, 0, 0], 0]]},
    ])
    return cases


def main():
    cases = create_cases()
    destination = ROOT / 'fixtures/qe_cases.json'
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps({'format': 'Inherited Choice-DI JSON packets; V1 target guard',
                                       'cases': cases}, indent=2) + '\n')
    for case in cases:
        if case['name'].startswith('expanded_QE_'):
            (ROOT / ('fixtures/qe_' + case['name'][12:] + '.json')).write_text(
                json.dumps(case['packet'], indent=2) + '\n')
    print(json.dumps({'case_count': len(cases), 'output': str(destination)}))


if __name__ == '__main__':
    main()
