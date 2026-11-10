"""Untrusted scalar-R certificate producer, adapted from generated-assumptions.

Named syntax/serializer are inherited from the pinned ProveIt archive.
Here every recursion is successor-seeded: R(0,a;h)=S(a).
This generator is not imported by any checker. It builds finite examples,
not a verified universal compilation of the arithmetic metatheorem.
"""
import copy
import json
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent
def V(name):
    return ('v', name)

def S(term):
    return ('s', term)

def R(counter, initial, state, update):
    return ('i', counter, initial, state, update)

def Eq(left, right):
    return ('eq', left, right)

def Q(variable, body):
    return ('q', variable, body)

def D(witness, index, body):
    return ('d', witness, index, body)

def C(index, initial, positive):
    return R(index, initial, '_unused_state', positive)

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
        return R(substitute(n, variable, value), substitute(a, variable, value),
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
    """Prove Q_y (R(y,initial;u.u)=initial) by literal-equation induction."""
    y, x, u = prefix + '_y', prefix + '_x', prefix + '_u'
    z, a, v = prefix + '_z', prefix + '_a', prefix + '_v'
    body = Eq(R(V(y), initial, u, V(u)), S(initial))
    current = R(V(z), initial, u, V(u))
    following = R(S(V(z)), initial, u, V(u))
    step = transport(hyp(Eq(current, S(initial))), v, Eq(following, V(v)),
                     computation(Eq(following, current)))
    paired = D(x, y, body)
    intro = introduction(paired, 0, z, 'progress', step)
    return elimination(intro, a, hyp(Q(y, body)))

def nested_identity_closure():
    """Prove Q_a Q_n (R(n,a;u.u)=a), preserving an outer parameter."""
    outer_y, outer_x, outer_z, outer_a = 'outer_y', 'outer_x', 'outer_z', 'outer_a'
    inner_y, inner_u = 'inner_y', 'inner_u'
    body = Q(inner_y, Eq(R(V(inner_y), V(outer_y), inner_u, V(inner_u)), S(V(outer_y))))
    paired = D(outer_x, outer_y, body)
    step = identity_closure('inner', initial=S(V(outer_z)))
    intro = introduction(paired, 0, outer_z, 'case', step)
    return elimination(intro, outer_a, hyp(Q(outer_y, body)))

def compute(term):
    _, n, seed, state, body = term
    if n == 0:
        rhs = S(seed)
    else:
        assert n[0] == 's'
        rhs = substitute(body, state, R(n[1], seed, state, body))
    return computation(Eq(term, rhs))

def reflexivity(term, name='refl_hole'):
    proof = compute(R(ONE, 0, name + '_state', term))
    return transport(proof, name, Eq(V(name), term), proof)

def symmetry(proof, name='sym_hole'):
    _, s, _ = proof['goal']
    return transport(proof, name, Eq(V(name), s), reflexivity(s, name + '_r'))

def transitivity(first, second, name='trans_hole'):
    _, s, middle = first['goal']
    assert second['goal'][1] == middle
    return transport(second, name, Eq(s, V(name)), first)

def congruence(proof, transform, name='cong_hole'):
    _, s, _ = proof['goal']
    return transport(proof, name, Eq(transform(s), transform(V(name))),
                     reflexivity(transform(s), name + '_r'))

def make_closure(index, body, step_builder, mode='progress', prefix='closure'):
    x, z, a = prefix + '_x', prefix + '_z', prefix + '_a'
    goal = D(x, index, body)
    premise = step_builder(V(z))
    intro = introduction(goal, ONE, z, mode, premise)
    return elimination(intro, a, hyp(Q(index, body)))

def neutral(major, continuation):
    assert major['goal'][0] in ('eq', 'q')
    return node('Neutral', continuation['goal'], major=major,
                continuation=continuation)

class Emitter:
    """Serialize a named derivation, independently of checker code.

    This emitter models symbolic rule premises and contexts. It never calls
    the checker's opening routine and never executes its dispatcher. Every
    command consumes a fresh label, even when that label is administrative.
    """
    def __init__(self, allow_forbidden_compound_progress=False):
        self.floor = 0
        self.parameters = {}
        self.instructions = []
        self.trace = []
        self.allow_forbidden = allow_forbidden_compound_progress

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
            return [self.term(term[1], ('_zero',) + env, hole)]
        if tag == 'i':
            _, n, seed, state, body = term
            return [self.term(n, ('_zero', '_zero') + env, hole),
                    self.term(seed, ('_zero', '_zero') + env, hole),
                    self.term(body, (state, state) + env, hole)]
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

    def allocate(self, name=None):
        self.floor -= 1
        if name is not None:
            assert name not in self.parameters
            self.parameters[name] = self.floor

    def emit(self, proof, context):
        goal = self.formula(proof['goal'])
        if goal in context:
            self.trace.append({'rule': 'Hyp', 'goal': goal,
                               'floor': self.floor, 'instruction': None})
            return
        rule = proof['rule']
        if rule == 'Hyp':
            raise ValueError('Unproved producer hypothesis: ' + repr(goal))
        position = len(self.instructions)
        event = {'rule': rule, 'goal': goal, 'floor': self.floor,
                 'instruction': position, 'mode': proof.get('mode')}
        self.trace.append(event)
        if rule == 'Computation':
            _, source, rhs = proof['goal']
            assert compute(source)['goal'] == proof['goal']
            _, counter, seed, state, body = source
            if counter == 0:
                previous = source
                step = 0
            else:
                if counter[0] != 's':
                    raise ValueError('Computation requires zero or a successor')
                previous = R(counter[1], seed, state, body)
                step = 1
            self.instructions.append([0, self.term(previous), step, 0])
            self.allocate()
            # The newly inserted axiom closes the continuation immediately.
            self.trace.append({'rule': 'InsertedHyp', 'goal': goal,
                               'floor': self.floor, 'instruction': None})
            return
        if rule in ('Tr', 'QE'):
            major = self.formula(proof['major']['goal'])
            if rule == 'Tr':
                _, source, target = proof['major']['goal']
                packet = [major, self.term(source), self.term(target),
                          self.formula(proof['motive'], hole=proof['variable'])]
            else:
                packet = [major, 0, self.term(proof['target']), major[0]]
            self.instructions.append(packet)
            self.emit(proof['major'], context)
            self.allocate()
            self.emit(proof['minor'], context + [[]])
            return
        if rule == 'Neutral':
            major = self.formula(proof['major']['goal'])
            packet = ([major, major[0], major[1], [1, major[1]]]
                      if proof.get('matching_endpoints') else [major, None, None, 0])
            self.instructions.append(packet)
            self.emit(proof['major'], context)
            self.allocate()
            self.emit(proof['continuation'], context + [[]])
            return
        if rule == 'DI':
            witness = self.term(proof['witness'])
            if witness == 0:
                # Existing zero-witness uses have an unused existential slot.
                witness = [[0], 0, 0]
            _, x, y, body = proof['goal']
            if proof['mode'] == 'progress' and body[0] != 'eq':
                assert self.allow_forbidden
            self.instructions.append([[] if proof['mode'] == 'case' else 0,
                                      0, 0, witness])
            self.allocate(proof['eigen'])
            current = V(proof['eigen']) if proof['mode'] == 'progress' else 0
            opened = substitute(body, x, proof['witness'])
            local = substitute(opened, y, current)
            self.emit(proof['premise'], context + [self.formula(local)])
            del self.parameters[proof['eigen']]
            return
        if rule == 'DE':
            self.instructions.append([self.formula(proof['major']['goal']),
                                      0, 0, 0])
            self.emit(proof['major'], context)
            self.allocate(proof['eigen'])
            _, x, y, body = proof['major']['goal']
            local = Q(y, substitute(body, x, V(proof['eigen'])))
            self.emit(proof['continuation'], context + [self.formula(local)])
            del self.parameters[proof['eigen']]
            return
        raise ValueError(rule)

    def packet(self, proof):
        goal = self.formula(proof['goal'])
        self.emit(proof, [])
        packet = list(reversed(self.instructions)) + [goal]
        for event in self.trace:
            if event['instruction'] is not None:
                event['packet_index'] = len(self.instructions) - 1 - event['instruction']
        return packet

def nonvacuous_elimination():
    x, y, z, a, v = 'wit_x', 'wit_y', 'wit_z', 'wit_a', 'wit_v'
    body = Eq(C(V(y), 0, V(x)), ONE)
    formula = D(x, y, body)
    pack = introduction(formula, ONE, z, 'case',
                        compute(C(S(V(z)), 0, ONE)))
    local = Q(y, substitute(body, x, V(a)))
    step = specialize(hyp(local), S(V(v)), compute(C(0, 0, V(a))))
    unpack = introduction(formula, V(a), v, 'case', step)
    return elimination(pack, a, unpack)

def contextual_seed_congruence():
    """Equation induction under a retained, essential equality assumption.

    The outer case-DI premise is a gated version of 1=0. We derive equality
    of successor iterations from seeds 1 and 0 by genuine atomic induction,
    using the retained assumption for the base and the IH for the step.
    No explosion principle is used in the generated proof.
    """
    y, z = 'ctx_y', 'ctx_z'
    def loop(n, seed):
        return R(n, seed, 'ctx_state', S(V('ctx_state')))
    def matrix(n):
        return Eq(C(n, ONE, loop(n, ONE)), C(n, 0, loop(n, 0)))
    original = matrix(V(y))
    base_hyp = hyp(matrix(0))
    seed_eq = transitivity(symmetry(compute(C(0, ONE, loop(0, ONE))), 'ctx_sl'),
                          transitivity(base_hyp, compute(C(0, 0, loop(0, 0))), 'ctx_sr'),
                          'ctx_seed')
    n = 'ctx_ind_n'
    body = Eq(loop(V(n), ONE), loop(V(n), 0))
    base = transitivity(compute(loop(0, ONE)),
                        transitivity(seed_eq, symmetry(compute(loop(0, 0)), 'ctx_br'), 'ctx_bm'),
                        'ctx_bl')
    def step(k):
        ih = hyp(Eq(loop(k, ONE), loop(k, 0)))
        return transitivity(compute(loop(S(k), ONE)),
                            transitivity(congruence(ih, S, 'ctx_cs'),
                                         symmetry(compute(loop(S(k), 0)), 'ctx_r'), 'ctx_mid'),
                            'ctx_left')
    closure = make_closure(n, body, step, prefix='ctx_closure')
    at_target = specialize(closure, S(V(z)), base)
    conclusion = transitivity(compute(C(S(V(z)), ONE, loop(S(V(z)), ONE))),
                              transitivity(at_target,
                                           symmetry(compute(C(S(V(z)), 0, loop(S(V(z)), 0))),
                                                    'ctx_final_r'),
                                           'ctx_final_mid'), 'ctx_final_l')
    return introduction(D('ctx_unused', y, original), ONE, z, 'case', conclusion)

def gated_closure_of_equation(proof, prefix):
    _, value, zero = proof['goal']
    assert zero == ONE
    index = prefix + '_w'
    body = Eq(C(V(index), 0, value), ONE)
    def step(k):
        return transitivity(compute(C(S(k), 0, value)), proof, prefix + '_join')
    return make_closure(index, body, step, mode='case', prefix=prefix)

def equation_of_gated_closure(major, value, prefix):
    one = specialize(major, ONE, compute(C(0, 0, value)))
    comp = compute(C(ONE, 0, value))
    return transport(comp, prefix + '_hole', Eq(V(prefix + '_hole'), ONE), one)

def forbidden_compound_progress():
    y, z, state = 'bad_y', 'bad_z', 'bad_state'
    def value(n):
        return R(n, 0, state, V(state))
    def formula(n):
        return Q('bad_w', Eq(C(V('bad_w'), 0, value(n)), ONE))
    current = equation_of_gated_closure(hyp(formula(V(z))), value(V(z)), 'bad_extract')
    following = transitivity(compute(value(S(V(z)))), current, 'bad_step')
    lifted = gated_closure_of_equation(following, 'bad_lift')
    # Match alpha-renamed bound indices before the constructor's assertion.
    lifted['goal'] = formula(S(V(z)))
    return introduction(D('bad_unused', y, formula(V(y))), ONE, z, 'progress', lifted)

ONE = S(0)
TWO = S(ONE)

def build_cases():
    cases = []
    def add(name, proof, meaning, accept=True, allow_forbidden=False):
        emitter = Emitter(allow_forbidden)
        packet = emitter.packet(proof)
        cases.append(dict(name=name, accept=accept, meaning=meaning, packet=packet,
                          trace=emitter.trace, allocations=-emitter.floor))
        return cases[-1]
    add('R0_nonzero_seed', compute(R(0, TWO, 'r0_u', S(V('r0_u')))),
        'R0 yields the successor of a nonzero seed.')
    add('RS_used_state', compute(R(TWO, ONE, 'rs_u', S(V('rs_u')))),
        'RS substitutes a genuinely used scalar state.')
    add('RS_constant_body', compute(R(TWO, ONE, 'rsc_u', TWO)),
        'A constant body still requires the predecessor iterator to be valid.')
    add('RS_compound_previous_counter',
        compute(R(S(R(0, 0, 'compound_n_u', 0)), ONE, 'compound_state', S(V('compound_state')))),
        'The checker constructs a successor around an arbitrary prior-counter term.')
    add('reflexivity_zero', reflexivity(0), 'Reflexivity is derived from constant RS.')
    add('reflexivity_two', reflexivity(TWO), 'Reflexivity at a nonzero term.')
    add('equation_progress', identity_closure('id'),
        'An equation induction uses the induction hypothesis and RS.')
    major = identity_closure('spec')
    _, y, body = major['goal']
    add('compound_target_QE',
        specialize(major, S(R(TWO, ONE, 'target_u', S(V('target_u')))),
                   computation(substitute(body, y, 0))),
        'Q specialization at a compound numerical target.')
    add('nested_closure', nested_identity_closure(),
        'Compound case introduction retains a passive parameter through inner induction.')
    add('nonvacuous_DE', nonvacuous_elimination(),
        'A nonvacuous existential witness is opened, used, and discharged.')
    add('contextual_induction', contextual_seed_congruence(),
        'An essential retained equality supplies a base for equation induction.')
    term = R(0, ONE, 'under_q_state', 0)
    original = identity_closure('under_q', term)
    hole, y = 'under_q_hole', 'under_q_y'
    motive = Q(y, Eq(R(V(y), V(hole), 'under_q_u', V('under_q_u')), S(V(hole))))
    add('transport_under_Q', transport(compute(term), hole, motive, original),
        'Transport through a compound formula.')
    add('neutral_endpoints', neutral(compute(R(0, ONE, 'ne_u', 0)),
                                   compute(R(TWO, 0, 'ne_v', S(V('ne_v'))))),
        'A harmless endpoint mismatch is followed by a real proof.')
    mismatch = neutral(compute(R(0, ONE, 'nt_u', 0)),
                       compute(R(TWO, 0, 'nt_v', S(V('nt_v')))))
    mismatch['matching_endpoints'] = True
    add('neutral_target', mismatch,
        'Matching endpoints with a mismatched target leave the target unchanged.')
    add('compound_progress_forbidden', forbidden_compound_progress(),
        'A forged compound induction uses B(z); the kernel supplies B(0).', False, True)
    def raw(name, packet, meaning, accept=False):
        cases.append(dict(name=name, packet=packet, accept=accept, meaning=meaning))
    source = [0, 0, 0]
    raw('false_zero_one', [[0, source, 0, 0], [0, [0]]], 'Computations cannot prove 0=1.')
    raw('old_zero_seed_equation', [[0, source, 0, 0], [source, 0]],
        'The old I0 equation is false for the new successor-seeded R.')
    raw('free_label', [[0, source, 0, 0], [-1, -1]], 'Unallocated labels reject.')
    raw('bad_major', [[0, source, 0, 0], [[0, [0]], None, None, 0], [source, [0]]],
        'A false major cannot fall through into a successful continuation.')
    raw('false_after_neutral',
        [[0, source, 0, 0], [0, source, 0, 0], [[source, [0]], None, None, 0], [0, [0]]],
        'Neutral requests do not prove false targets.')
    raw('false_annotated_counter_equation',
        [[0, [[0, 0], 0, 0], 1, 0], [[[0, 0], 0, 0], 0]],
        'Constructing the successor prevents the false equation R(0,0;0)=0.')
    raw('base_ignores_counter_field', [[0, [[0, 0, 0], 0, 0], 0, 0], [source, [0]]],
        'A base packet constructs counter zero; its unused prior-counter field is inert.', True)
    raw('invalid_seed', [[0, [0, None, 1], 1, 0], [source, [0]]],
        'A used recursive image validates its entire seed and update.')
    raw('invalid_update', [[0, [0, 0, {}], 1, 0], [source, [0]]],
        'Mappings are not update syntax.')
    raw('exposed_update_alias', [[0, [0, 0, 5], 1, 0], [source, [0]]],
        'An exposed update coordinate forces validation of the old recursor.')
    raw('four_field_goal', [[0, source, 0, 0], [0, 0, 0, 0]],
        'Constructor arity checking remains charged.')
    forged = Emitter()
    forged.parameters['unallocated_global'] = -999
    raw('forged_parameter_reflexivity', forged.packet(reflexivity(V('unallocated_global'))),
        'A theorem-shaped packet still cannot name an unallocated global parameter.')
    for original_name, rule, field, value, new_name in [
        ('nonvacuous_DE', 'DI', 3, -999, 'future_DI_witness'),
        ('equation_progress', 'DI', 0, [], 'progress_replaced_by_base'),
        ('compound_target_QE', 'QE', 2, -999, 'future_QE_target')]:
        original_case = next(c for c in cases if c['name'] == original_name)
        packet = copy.deepcopy(original_case['packet'])
        event = next(e for e in original_case['trace'] if e['rule'] == rule)
        packet[event['packet_index']][field] = value
        raw(new_name, packet, 'Mutation of a substantive accepted derivation.')
    alias = Emitter().packet(reflexivity(0))
    alias.insert(-1, [0, [0, 3, 0], 0, 0])
    raw('fresh_witness_computation_alias', alias,
        'A safe generated equation has a known zero instance; later reflexivity closes.', True)
    return cases

def main():
    cases = build_cases()
    output = dict(format='Successor-seeded scalar R, generated assumptions',
                  scope='Finite proof packets, not a formal metatheorem', cases=cases)
    if '--check' in sys.argv:
        stored = json.loads((ROOT / 'cases.json').read_text())
        if output != stored:
            raise AssertionError('Recorded named proofs/packets differ from regeneration')
        for case in cases:
            if json.loads((ROOT / 'fixtures' / (case['name']+'.json')).read_text()) != case['packet']:
                raise AssertionError('Fixture differs: '+case['name'])
        print(json.dumps(dict(status='PASS', regenerated_packets=len(cases))))
        return
    (ROOT / 'cases.json').write_text(json.dumps(output, indent=2) + '\n')
    (ROOT / 'fixtures').mkdir(exist_ok=True)
    for old in (ROOT / 'fixtures').glob('*.json'):
        old.unlink()
    for case in cases:
        (ROOT / 'fixtures' / (case['name'] + '.json')).write_text(
            json.dumps(case['packet'], indent=2) + '\n')
    print(json.dumps(dict(cases=len(cases), positive=sum(c['accept'] for c in cases))))

if __name__ == '__main__':
    main()
