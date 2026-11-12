# Untrusted producer for the seed-dispatch checker.
# Derived from ProveIt uniform_predecessor/tests/producer.py and arity_calculus/tests/producer.py,
# fetched at ProveIt commit fb2dbd2a33c6b132671a54b029d0bf3cd98c633d.
# New work: simultaneous seed/predecessor normalization in expand_computation and initializer-driven dispatch.
# The checker does not import this producer.
"""Untrusted named proof producer for predecessor-generated computations.

Adapted from the verified flat-computation draft's tests/producer.py;
that file in turn attributes the generated-assumptions and named-specialization
producers. No candidate checker imports this module.

Inherited interface: arithmetic packets carry a predecessor p. New: a nonempty initializer selects arithmetic, and C=I(2,1;v.0) normalizes excluded zero values.
A truthy p constructs I(S p,a;h)=h(I(p,a;h)); a falsy p supplies I0.
Only a literal-zero successor predecessor needs the inherited box expansion.
Named arbitrary parameters therefore avoid two command records per step.
The inherited naming and scope discipline, logical examples, and semantic
negative controls remain in use.
"""
import copy
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


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


def compute(term):
    _, n, seed, state, body = term
    if n == 0:
        rhs = seed
    else:
        assert n[0] == 's'
        rhs = substitute(body, state, I(n[1], seed, state, body))
    return computation(Eq(term, rhs))


def reflexivity(term, name='refl_hole'):
    proof = compute(I(0, term, name + '_state', 0))
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


_box_serial = 0


def fresh_box_name(proof):
    """Choose a name absent from every binder and free name in this tree."""
    global _box_serial
    text = repr(proof)
    while True:
        _box_serial += 1
        name = '_counter_box_' + str(_box_serial)
        if name not in text:
            return name




def expand_computation(proof):
    """Normalize every computation leaf with one simultaneous transport.

    C=I(2,1;v.0) has a direct computation proof C=0. A fresh motive
    replaces a literal-zero initializer and a literal-zero predecessor
    simultaneously by the same variable. Substitution of C produces an
    allowed direct computation; substitution of 0 restores the requested
    equation. Passive zero occurrences in the update remain untouched.
    Every problematic computation leaf becomes exactly three native nodes:
    one transport with two direct computation premises.
    """
    _, source, actual = proof['goal']
    assert compute(source)['goal'] == proof['goal']
    _, counter, seed, state, update = source
    bad_seed = seed == 0
    bad_predecessor = counter != 0 and counter[0] == 's' and counter[1] == 0
    if not (bad_seed or bad_predecessor):
        return proof
    hole = fresh_box_name(proof) + '_normal'
    zero_alias = I(TWO, ONE, hole + '_state', 0)
    symbolic = I(S(V(hole)) if bad_predecessor else counter,
                 V(hole) if bad_seed else seed, state, update)
    motive = compute(symbolic)['goal']
    changed = substitute(symbolic, hole, zero_alias)
    result = transport(compute(zero_alias), hole, motive, compute(changed),
                       role='nonempty_seed_predecessor_normalization')
    assert result['goal'] == proof['goal']
    return result


def expand_proof(proof):
    if proof['rule'] == 'Computation':
        result = expand_computation(proof)
        return proof if result is proof else expand_proof(result)
    result = dict(proof)
    for key in ('major', 'minor', 'premise', 'continuation'):
        if key in proof:
            result[key] = expand_proof(proof[key])
    return result


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
                    return 2 * env.index(name) + 3
                if name == hole:
                    return 2 * len(env) + 3
                if name in self.parameters:
                    return self.parameters[name]
                raise ValueError('Unscoped producer variable: ' + name)
            if tag == 's':
                return [self.term(term[1], ('_zero', '_zero') + env, hole)]
            if tag == 'i':
                _, n, seed, state, body = term
                return [self.term(n, ('_zero',) + env, hole),
                        self.term(seed, ('_zero',) + env, hole),
                        self.term(body, (state,) + env, hole)]
            raise ValueError('Not a numerical term: ' + repr(term))

    def formula(self, formula, env=(), hole=None):
            tag = formula[0]
            if tag == 'eq':
                return [self.term(formula[1], env, hole),
                        self.term(formula[2], env, hole)]
            if tag == 'q':
                return [self.formula(formula[2], (formula[1],) + env, hole)] * 3
            if tag == 'd':
                _, x, y, body = formula
                return [self.formula(body, (y, x) + env, hole)]
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
                 'instruction': position, 'mode': proof.get('mode'), 'role': proof.get('role')}
        self.trace.append(event)
        if rule == 'Computation':
            _, source, rhs = proof['goal']
            assert compute(source)['goal'] == proof['goal']
            counter, seed, update = self.term(source)
            self.instructions.append([[], counter[0] if counter else 0, seed, update])
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
            saved_floor = self.floor
            self.emit(proof['major'], context)
            self.floor = saved_floor
            self.allocate()
            self.emit(proof['minor'], context + [[]])
            return
        if rule == 'Neutral':
            major = self.formula(proof['major']['goal'])
            packet = ([major, major[0], major[1], [1, major[1]]]
                      if proof.get('matching_endpoints') else [major, None, None, 0])
            self.instructions.append(packet)
            saved_floor = self.floor
            self.emit(proof['major'], context)
            self.floor = saved_floor
            self.allocate()
            self.emit(proof['continuation'], context + [[]])
            return
        if rule == 'DI':
            witness = self.term(proof['witness'])
            _, x, y, body = proof['goal']
            if proof['mode'] == 'progress' and body[0] != 'eq':
                assert self.allow_forbidden
            self.instructions.append([[], 0, [] if proof['mode'] == 'case' else 0, witness])
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
            saved_floor = self.floor
            self.emit(proof['major'], context)
            self.floor = saved_floor
            self.allocate(proof['eigen'])
            _, x, y, body = proof['major']['goal']
            local = Q(y, substitute(body, x, V(proof['eigen'])))
            self.emit(proof['continuation'], context + [self.formula(local)])
            del self.parameters[proof['eigen']]
            return
        raise ValueError(rule)

    def packet(self, proof):
        proof = expand_proof(proof)
        goal = self.formula(proof['goal'])
        self.emit(proof, [])
        packet = list(reversed(self.instructions)) + [goal]
        for event in self.trace:
            if event['instruction'] is not None:
                event['packet_index'] = len(self.instructions) - 1 - event['instruction']
        return packet


def nonvacuous_elimination():
    x, y, z, a, v = 'wit_x', 'wit_y', 'wit_z', 'wit_a', 'wit_v'
    body = Eq(C(V(y), ONE, V(x)), ONE)
    formula = D(x, y, body)
    pack = introduction(formula, ONE, z, 'case',
                        compute(C(S(V(z)), ONE, ONE)))
    local = Q(y, substitute(body, x, V(a)))
    step = specialize(hyp(local), S(V(v)), compute(C(0, ONE, V(a))))
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
        return I(n, seed, 'ctx_state', S(V('ctx_state')))
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
    assert zero == 0
    index = prefix + '_w'
    body = Eq(C(V(index), 0, value), 0)
    def step(k):
        return transitivity(compute(C(S(k), 0, value)), proof, prefix + '_join')
    return make_closure(index, body, step, mode='case', prefix=prefix)


def equation_of_gated_closure(major, value, prefix):
    one = specialize(major, ONE, compute(C(0, 0, value)))
    comp = compute(C(ONE, 0, value))
    return transport(comp, prefix + '_hole', Eq(V(prefix + '_hole'), 0), one)


def forbidden_compound_progress():
    y, z, state = 'bad_y', 'bad_z', 'bad_state'
    def value(n):
        return I(n, 0, state, V(state))
    def formula(n):
        return Q('bad_w', Eq(C(V('bad_w'), 0, value(n)), 0))
    current = equation_of_gated_closure(hyp(formula(V(z))), value(V(z)), 'bad_extract')
    following = transitivity(compute(value(S(V(z)))), current, 'bad_step')
    lifted = gated_closure_of_equation(following, 'bad_lift')
    # Match alpha-renamed bound indices before the constructor's assertion.
    lifted['goal'] = formula(S(V(z)))
    return introduction(D('bad_unused', y, formula(V(y))), ONE, z, 'progress', lifted)


def build_cases():
    global _box_serial
    _box_serial = 0
    cases = []
    def add(name, proof, meaning, accept=True, allow_forbidden=False):
        emitter = Emitter(allow_forbidden)
        packet = emitter.packet(proof)
        cases.append({'name': name, 'accept': accept, 'meaning': meaning,
                      'packet': packet, 'proof_tree': proof, 'trace': emitter.trace,
                      'allocations': -emitter.floor})
        return cases[-1]
    add('IS_boxed_zero_predecessor', compute(I(ONE, ONE, 'boxzero_u', S(V('boxzero_u')))),
        'The ordinary IS instance at scalar predecessor zero is expanded by simultaneous C=I(2,1;v.0) normalization.')
    zero_x, zero_y, zero_z = 'zero_x', 'zero_y', 'zero_z'
    zero_body = Eq(C(V(zero_y), 0, V(zero_x)), 0)
    zero_goal = D(zero_x, zero_y, zero_body)
    add('nonvacuous_literal_zero_witness',
        introduction(zero_goal, 0, zero_z, 'case',
                     compute(C(S(V(zero_z)), 0, 0))),
        'Case DI uses the actual packet witness 0, and the existential coordinate occurs in its matrix.')
    add('I0_arbitrary_seed', compute(I(0, TWO, 'i0_u', S(V('i0_u')))),
        'Zero computation with a nonzero initializer; inserts a checked equation.')
    add('IS_state_used', compute(I(TWO, ONE, 'is_u', S(V('is_u')))),
        'Successor computation whose update actually uses the recursive state.')
    add('IS_constant_update', compute(I(TWO, ONE, 'isc_u', TWO)),
        'Successor computation with constant update; the final source is validated even when the recursive image is unused.')
    add('equality_transport_reflexivity', reflexivity(TWO),
        'Reflexivity derived from I0 and equality transport, with no reflexivity opcode.')
    add('atomic_progress_closure', identity_closure('id'),
        'A real equation-induction step uses both its induction hypothesis and IS.')
    major = identity_closure('spec')
    _, y, body = major['goal']
    add('Q_arbitrary_term_specialization',
        specialize(major, S(I(TWO, ONE, 'target_u', S(V('target_u')))),
                   computation(substitute(body, y, 0))),
        'Specialization at a compound numerical term, with a separately proved base.')
    add('compound_case_nested_closure', nested_identity_closure(),
        'Case introduction above Q, with a passive parameter retained by nested equation induction.')
    add('nonvacuous_witness_DE_roundtrip', nonvacuous_elimination(),
        'An actual existential witness is opened, used, and discharged without escaping.')
    add('contextual_induction_seed_congruence', contextual_seed_congruence(),
        'Under the retained gated equality 1=0, induction proves seed congruence; the step uses IH.')
    term = I(0, ONE, 'compound_seed_state', 0)
    original = identity_closure('compound_tr', term)
    y, hole = 'compound_tr_y', 'compound_hole'
    motive = Q(y, Eq(I(V(y), V(hole), 'compound_tr_u', V('compound_tr_u')), V(hole)))
    add('transport_under_Q', transport(compute(term), hole, motive, original),
        'Equality transport through a quantified formula, rather than only an atomic equation.')
    add('neutral_wrong_endpoints_then_valid_proof',
        neutral(compute(I(0, ONE, 'neutral_u', 0)),
                compute(I(TWO, 0, 'neutral_v', S(V('neutral_v'))))),
        'A proved major with mismatched endpoint fields leaves the target unchanged; later proof succeeds.')
    mismatch = neutral(compute(I(0, ONE, 'neutral2_u', 0)),
                       compute(I(TWO, 0, 'neutral2_v', S(V('neutral2_v')))))
    mismatch['matching_endpoints'] = True
    add('neutral_target_mismatch_then_valid_proof', mismatch,
        'Endpoints identify the proved equation, but the target formula fails to match; later proof succeeds.')
    add('forbidden_compound_progress', forbidden_compound_progress(),
        'The forged derivation uses B(z) for a compound matrix; the actual kernel supplies B(0).',
        accept=False, allow_forbidden=True)

    def raw(name, packet, meaning, accept=False):
        cases.append({'name': name, 'packet': packet, 'accept': accept, 'meaning': meaning})
    source = [0, 0, 0]
    raw('canonical_false', [[None, 0, 0, 0], [0, [0]]],
        'A genuine flat I0 computation cannot prove 0=1.')
    raw('wrong_computation_endpoint', [[None, 0, [0], 0], [[0, [0], 0], 0]],
        'The generated I0 equation has endpoint 1; it cannot close a requested endpoint 0.')
    raw('failed_major_does_not_fall_through',
        [[None, 0, 0, 0], [[0, [0]], None, None, 0], [source, 0]],
        'An attempted neutral command must first prove its false major.')
    raw('neutral_mismatch_cannot_prove_false',
        [[None, 0, 0, 0], [None, 0, 0, 0], [[source, 0], None, None, 0], [0, [0]]],
        'A proved harmless major cannot make an unmatched endpoint command prove 0=1.')
    raw('free_parameter_in_closed_goal', [[None, 0, 0, 0], [-1, -1]],
        'The requested closed goal contains an unallocated negative label.')
    raw('out_of_range_seed_zero_alias', [[None, 0, -999, 0], [source, 0]],
        'The permissive opener replaces the out-of-range seed by zero, yielding the valid I0(0,0)=0 axiom. This is an explicit safe raw alias, not an allocated future parameter.', accept=True)
    raw('next_parameter_seed_cannot_close_unrelated_goal',
        [[None, 0, -1, 0], [source, 0]],
        'The permissive zero-instance generator may name its fresh local witness, but cannot close an unrelated goal.')
    raw('missing_seed', [[None, [[]], None, 0], [source, 0]],
        'A constant update must not hide an invalid seed in the generated source equation.')
    raw('unboxed_scalar_predecessor_constant_update',
        [[None, [0], 0, 0], [[[0], 0, 0], 0]],
        'The old whole-counter packet [0] is now read as predecessor S0, so it cannot close the requested IS-at-zero equation.')
    raw('two_child_counter_constant_update',
        [[None, [0, 0], 0, 0], [[[0, 0], 0, 0], 0]],
        'The predecessor packet always constructs an outer successor; it cannot close the displayed equation with a binary numerical-zero counter.')
    raw('three_child_counter_constant_update',
        [[None, [0, 0, 0], 0, 0], [source, 0]],
        'A ternary predecessor constructs a successor computation, not the unrelated requested I0 equation.')
    raw('invalid_update_mapping', [[None, [[]], 0, {}], [source, 0]],
        'This malformed update packet cannot establish the requested equation; the primary and byte profiles also reject mapping syntax outright.')
    raw('arity_four_goal', [[None, 0, 0, 0], [0, 0, 0, 0]],
        'This particular certificate for a four-child truth alias is rejected; the decoder admits surplus arities as truth, so this is not a general arity-rejection claim.')
    # Mutations of actual positive derivations preserve realistic certificate shape.
    witness_case = next(c for c in cases if c['name'] == 'nonvacuous_witness_DE_roundtrip')
    invalid = copy.deepcopy(witness_case['packet'])
    event = next(e for e in witness_case['trace'] if e['rule'] == 'DI')
    invalid[event['packet_index']][3] = -999
    raw('unallocated_DI_witness', invalid,
        'A witness cannot refer to a parameter allocated in the future.')
    induction_case = next(c for c in cases if c['name'] == 'atomic_progress_closure')
    invalid = copy.deepcopy(induction_case['packet'])
    event = next(e for e in induction_case['trace'] if e['rule'] == 'DI' and e['mode'] == 'progress')
    invalid[event['packet_index']][0] = []
    raw('induction_step_with_base_only_context', invalid,
        'Replacing the genuine equation induction hypothesis by the base breaks this proof.')
    specialization_case = next(c for c in cases if c['name'] == 'Q_arbitrary_term_specialization')
    invalid = copy.deepcopy(specialization_case['packet'])
    event = next(e for e in specialization_case['trace'] if e['rule'] == 'QE')
    invalid[event['packet_index']][2] = -999
    raw('unallocated_Q_target', invalid,
        'An endpoint requesting an unallocated numerical label is not a neutral conversion.')
    return cases



def main():
    cases = build_cases()
    output = {'format': 'Seed-dispatch arithmetic [m,p,a,h] with falsy m and truthy a; paired introductions have a=0; unary D and triplicate Q codec',
              'scope': 'Named proof examples and targeted rejection controls; not a formal soundness proof',
              'cases': cases}
    (ROOT / 'cases.json').write_text(json.dumps(output, indent=2) + '\n')
    (ROOT / 'fixtures').mkdir(exist_ok=True)
    for case in cases:
        (ROOT / 'fixtures' / (case['name'] + '.json')).write_text(
            json.dumps(case['packet'], indent=2) + '\n')
    print(json.dumps({'case_count': len(cases), 'positive': sum(c['accept'] for c in cases),
                      'negative': sum(not c['accept'] for c in cases)}))


if __name__ == '__main__':
    main()

