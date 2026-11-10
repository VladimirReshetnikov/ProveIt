# Adapted for successor-seeded SR by the arithmetic_core research agent.
# The named tree uses the inherited internal tag 'i' for R; semantics are SR.
# Complete source provenance is retained in the inherited header below.
# Adapted named-syntax constructors from ProveIt docs/drafts/
# ipra_named_specialization_2026-11-10.zip, code/qe_producer.py.
# The proof emitter below is new: it implements four explicit endpoint fields,
# computation-axiom insertion, neutral conversions, and fresh allocation at
# every non-hypothesis command. It is not imported by the trusted checker.
"""Untrusted named-syntax producer for direct native SR computation-insertion certificates.

No checker imports this file. Named proof trees are expanded into complete
four-field packets; every arithmetic fact expands into explicit checked
computation and transport nodes.
The zero-witness convenience in Emitter is used only with an unused witness
coordinate. This finite example producer is not a general proof translator.
"""
import copy
import json
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


def T(index, initial, positive):
    return R(index, initial, '_unused_state', positive)


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
            self.instructions.append([0, self.term(source), 0, 0])
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
                witness = [0, 0]
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



# The remainder is new SR-specific untrusted proof construction.
_serial = 0


def fresh(label='name'):
    global _serial
    _serial += 1
    return 'sr_' + label + '_' + str(_serial)


def z_term(n):
    return R(n, 0, 'sr_macro_Z_state', 0)


def n_term(n):
    state = 'sr_macro_N_state'
    return z_term(R(n, 0, state, z_term(V(state))))


def p2_term(n):
    return n_term(S(n))


def normalize(term, fuel=400):
    """Produce a finite equational rewrite proof, not an evaluated oracle.

    Only a recursor whose counter is syntactically zero or successor is
    unfolded. An unknown counter is left untouched. Bodies under a binder
    are never rewritten by an unproved extensionality principle.
    """
    if fuel <= 0:
        raise ValueError('Finite normalizer fuel exhausted')
    if term == 0 or term[0] == 'v':
        return reflexivity(term, fresh('normal_refl'))
    if term[0] == 's':
        child = normalize(term[1], fuel-1)
        if child['goal'][2] == term[1]:
            return reflexivity(term, fresh('normal_refl'))
        return congruence(child, S, fresh('normal_S'))
    if term[0] != 'i':
        raise ValueError('Numerical normalizer received a formula')
    _, counter, seed, state, body = term
    counter_proof = normalize(counter, fuel-1)
    new_counter = counter_proof['goal'][2]
    current = R(new_counter, seed, state, body)
    if new_counter != counter:
        prefix = congruence(counter_proof,
                            lambda x: R(x, seed, state, body),
                            fresh('normal_counter'))
    else:
        prefix = None
    if new_counter != 0 and new_counter[0] != 's':
        return prefix or reflexivity(term, fresh('normal_refl'))
    contracted = compute(current)
    proof = (transitivity(prefix, contracted, fresh('normal_contract'))
             if prefix else contracted)
    rhs = proof['goal'][2]
    suffix = normalize(rhs, fuel-1)
    if suffix['goal'][2] != rhs:
        proof = transitivity(proof, suffix, fresh('normal_tail'))
    return proof


def finite_equation(goal):
    """Prove equality by explicitly generated finite SR computations."""
    assert goal[0] == 'eq'
    left, right = normalize(goal[1]), normalize(goal[2])
    if left['goal'][2] != right['goal'][2]:
        raise ValueError('Finite normal forms differ: ' + repr(goal))
    return transitivity(left, symmetry(right, fresh('finite_sym')),
                        fresh('finite_join'))


def sr_identity_closure(prefix='id', initial=0):
    """Q_y R(y,a;u.u)=S a, with genuine use of the equation IH."""
    y, x, u = prefix + '_y', prefix + '_x', prefix + '_u'
    z, a = prefix + '_z', prefix + '_a'
    body = Eq(R(V(y), initial, u, V(u)), S(initial))
    current = R(V(z), initial, u, V(u))
    following = R(S(V(z)), initial, u, V(u))
    step = transitivity(compute(following), hyp(Eq(current, S(initial))),
                        fresh('identity_step'))
    intro = introduction(D(x, y, body), 0, z, 'progress', step)
    return elimination(intro, a, hyp(Q(y, body)))


def sr_nested_identity_closure():
    outer_y, outer_z = 'sr_outer_y', 'sr_outer_z'
    inner_y, inner_u = 'sr_inner_y', 'sr_inner_u'
    body = Q(inner_y, Eq(R(V(inner_y), V(outer_y), inner_u, V(inner_u)),
                        S(V(outer_y))))
    goal = D('sr_outer_x', outer_y, body)
    step = sr_identity_closure('sr_inner', S(V(outer_z)))
    intro = introduction(goal, ONE, outer_z, 'case', step)
    return elimination(intro, 'sr_outer_a', hyp(Q(outer_y, body)))


def sr_nonvacuous_roundtrip():
    x, y, z, a, w = [fresh('witness') for _ in range(5)]
    body = Eq(T(V(y), 0, V(x)), V(x))
    goal = D(x, y, body)
    pack = introduction(goal, ONE, z, 'case',
                        compute(T(S(V(z)), 0, ONE)))
    opened = substitute(body, x, V(a))
    local_base = substitute(opened, y, 0)
    positive = specialize(hyp(Q(y, opened)), S(V(w)), hyp(local_base))
    unpack = introduction(goal, V(a), w, 'case', positive)
    return elimination(pack, a, unpack)


_decoder_proof = None


def decoder_closure():
    """Actual Q_x[p2(S(Zx))=Zx] using native compound-free CASE.

    Both branches are justified by finite SR computations. No arithmetic
    evaluator or externally supplied Boolean-decoder theorem is trusted.
    """
    global _decoder_proof
    if _decoder_proof is None:
        y = 'sr_decoder_y'
        body = Eq(p2_term(S(z_term(V(y)))), z_term(V(y)))
        def step(k):
            return finite_equation(substitute(body, y, S(k)))
        _decoder_proof = make_closure(y, body, step, mode='case',
                                     prefix='sr_decoder_case')
    return _decoder_proof


def decoder_at(term):
    closure = decoder_closure()
    _, y, body = closure['goal']
    base = finite_equation(substitute(body, y, 0))
    return specialize(closure, term, base, role='Boolean_decoder_specialization')


def restricted_implication_identity(b):
    """Derive Imp(b=0,b=0) from finite decoding, with b literally Z(r).

    The case-introduction premise really uses its retained S b = 1
    assumption. Applying p2 and the checked decoder derives b=0; there is
    no general successor-injectivity opcode and no assumption of P.
    """
    assert b[0] == 'i' and b[2] == 0 and b[4] == 0
    raw_boolean_source = b[1]
    x, y, z = fresh('imp_x'), fresh('imp_y'), fresh('imp_z')
    matrix = Eq(T(V(y), b, b), T(V(y), 0, 0))
    zero_matrix = substitute(matrix, y, 0)
    left_zero = compute(zero_matrix[1])
    right_zero = compute(zero_matrix[2])
    successor_eq = transitivity(
        symmetry(left_zero, fresh('imp_left_sym')),
        transitivity(hyp(zero_matrix), right_zero, fresh('imp_zero_join')),
        fresh('imp_successor_eq'))
    decoded_assumption = congruence(successor_eq, p2_term, fresh('imp_decode'))
    boolean_decoder = decoder_at(raw_boolean_source)
    decode_one = normalize(p2_term(ONE))
    assert decode_one['goal'][2] == 0
    conclusion = transitivity(
        symmetry(boolean_decoder, fresh('imp_decoder_sym')),
        transitivity(decoded_assumption, decode_one, fresh('imp_decoder_join')),
        fresh('imp_boolean_eq'))
    assert conclusion['goal'] == Eq(b, 0)
    positive_matrix = substitute(matrix, y, S(V(z)))
    premise = transitivity(
        compute(positive_matrix[1]),
        transitivity(conclusion, symmetry(compute(positive_matrix[2]),
                                         fresh('imp_right_sym')),
                     fresh('imp_positive_join')),
        fresh('imp_positive'))
    return introduction(D(x, y, matrix), ONE, z, 'case', premise)


def restricted_implication_identity_closure():
    """Q_n Imp(N(n)=0,N(n)=0), with a genuinely variable Boolean term."""
    outer_y, outer_x, outer_z, outer_a = [fresh('imp_outer') for _ in range(4)]
    # Build the successor premise first, then uniformly abstract its counter.
    step = restricted_implication_identity(n_term(S(V(outer_z))))
    # The named syntax has no general inverse substitution. Build a template
    # by replacing that exact S(z) subtree, avoiding all unrelated binders.
    def replace_exact(tree, old, new):
        if tree == old:
            return new
        if not isinstance(tree, tuple):
            return tree
        return tuple(replace_exact(x, old, new) for x in tree)
    body = replace_exact(step['goal'], S(V(outer_z)), V(outer_y))
    assert substitute(body, outer_y, S(V(outer_z))) == step['goal']
    intro = introduction(D(outer_x, outer_y, body), ONE, outer_z, 'case', step)
    return elimination(intro, outer_a, hyp(Q(outer_y, body)))


def sr_forbidden_compound_progress():
    y, z, state, index = [fresh('bad_compound') for _ in range(4)]
    def value(n):
        return R(n, 0, state, V(state))
    def formula(n):
        return Q(index, Eq(T(V(index), 0, value(n)), ONE))
    current_gate = specialize(hyp(formula(V(z))), ONE,
                              compute(T(0, 0, value(V(z)))))
    hole = fresh('bad_extract')
    current = transport(compute(T(ONE, 0, value(V(z)))), hole,
                        Eq(V(hole), ONE), current_gate)
    following = transitivity(compute(value(S(V(z)))), current,
                             fresh('bad_following'))
    lifted_body = Eq(T(V(index), 0, value(S(V(z)))), ONE)
    def lifted_step(k):
        return transitivity(compute(T(S(k), 0, value(S(V(z))))), following,
                            fresh('bad_lifted_step'))
    lifted = make_closure(index, lifted_body, lifted_step, mode='case',
                          prefix=fresh('bad_lift'))
    assert lifted['goal'] == formula(S(V(z)))
    return introduction(D(fresh('bad_unused'), y, formula(V(y))), ONE, z,
                        'progress', lifted)


def build_sr_cases():
    cases = []
    def add(name, proof, meaning, accept=True, allow_forbidden=False):
        emitter = Emitter(allow_forbidden)
        packet = emitter.packet(proof)
        cases.append({'name': name, 'accept': accept, 'meaning': meaning,
                      'packet': packet, 'trace': emitter.trace,
                      'allocations': -emitter.floor})
        return cases[-1]
    add('SR0_nonzero_seed', compute(R(0,TWO,'sr0_u',S(V('sr0_u')))),
        'SR zero computation returns the successor of a nonzero initializer.')
    add('SRS_state_used', compute(R(TWO,ONE,'srs_u',S(V('srs_u')))),
        'The successor update actually uses the recursive state.')
    add('SRS_constant_update', compute(R(TWO,ONE,'srsc_u',TWO)),
        'A constant update still requires a valid recursive predecessor image.')
    add('SR_reflexivity_from_positive_computation', reflexivity(TWO, fresh('refl')),
        'Reflexivity derives from R(1,0;const t)=t and transport.')
    atomic = add('SR_actual_atomic_induction', sr_identity_closure('sr_id'),
        'Literal equation induction uses its induction hypothesis and SRS.')
    closure = sr_identity_closure('sr_spec')
    _, y, body = closure['goal']
    target = S(R(TWO,ONE,'sr_target_u',S(V('sr_target_u'))))
    specialized = add('SR_Q_compound_target',
        specialize(closure,target,compute(substitute(body,y,0)[1])),
        'Closure specialization at a compound term, with the actual SR base.')
    add('SR_compound_case_nested_induction', sr_nested_identity_closure(),
        'Compound case introduction retains an outer parameter for nested atomic induction.')
    witness = add('SR_nonvacuous_D_Q_roundtrip',sr_nonvacuous_roundtrip(),
        'A nonvacuous witness is opened, used in a closure, and discharged.')
    term = R(0,ONE,'sr_transport_seed',0)
    original = sr_identity_closure('sr_transport',term)
    hole = fresh('transport_hole')
    motive = Q('sr_transport_y', Eq(R(V('sr_transport_y'),V(hole),
                                     'sr_transport_u',V('sr_transport_u')),S(V(hole))))
    add('SR_transport_under_Q',transport(compute(term),hole,motive,original),
        'Equality transport changes an initializer below a Q binder.')
    decoder_case = add('SR_Boolean_decoder_native_CASE',decoder_closure(),
        'Closed Q_x[p2(S(Zx))=Zx], derived by native case introduction and finite SR computations.')
    add('SR_Boolean_decoder_specialization',decoder_at(target),
        'The native decoder closure is specialized with a separately proved zero case.')
    implication_case = add('SR_restricted_Boolean_implication',restricted_implication_identity_closure(),
        'A nested native D implication cancels successor only on a variable Boolean, using the checked decoder.')
    add('SR_reject_compound_progress',sr_forbidden_compound_progress(),
        'A forged compound induction step needs Q at z; the actual rule supplies only Q at zero.',
        accept=False,allow_forbidden=True)

    def raw(name,packet,meaning):
        cases.append({'name':name,'accept':False,'packet':packet,'meaning':meaning})
    source = [0,0,0]
    raw('SR_reject_old_I0',[[0,source,0,0],[source,0]],
        'The old zero-initialized computation is false: SR(0,0;0)=1, not0.')
    raw('SR_reject_false',[[0,source,0,0],[0,[0]]],
        'A genuine SR computation does not prove0=1.')
    raw('SR_reject_missing_seed',[[0,[[0],None,0],0,0],[[[0],None,0],0]],
        'A constant update cannot hide an invalid seed.')
    bad_counter = [[0,0],0,0]
    raw('SR_reject_two_child_counter',[[0,bad_counter,0,0],[bad_counter,0]],
        'A two-child counter is not a successor.')
    bad_counter = [[0,0,0],0,0]
    raw('SR_reject_three_child_counter',[[0,bad_counter,0,0],[bad_counter,0]],
        'A three-child counter cannot pass the eager predecessor-shape check.')
    raw('SR_reject_future_goal_parameter',[[0,source,0,0],[-1,-1]],
        'Closed goals cannot contain unallocated parameter labels.')
    raw('SR_reject_arity_four',[[0,source,0,0],[0,0,0,0]],
        'The sorted codec rejects arity four.')
    raw('SR_reject_failed_major',
        [[0,source,0,0],[[0,[0]],None,None,0],[source,[0]]],
        'A false major cannot fall through into an otherwise valid computation.')
    packet=copy.deepcopy(implication_case['packet'])
    inner_intro=[event for event in implication_case['trace'] if event['rule']=='DI'][1]
    packet[inner_intro['packet_index']][0]=0
    raw('SR_reject_BI_without_zero_assumption',packet,
        'The Boolean implication proof needs its actual zero-case antecedent, not a progress assumption.')
    _,decoder_y,decoder_body=decoder_closure()['goal']
    packet=copy.deepcopy(decoder_case['packet'])
    packet[-1]=Emitter().formula(Q(decoder_y,Eq(decoder_body[1],S(decoder_body[2]))))
    raw('SR_reject_shifted_decoder_target',packet,
        'The valid Boolean decoder proof cannot prove its false successor-shifted target.')
    for case,rule,field,replacement,name,meaning in [
        (witness,'DI',3,-999,'SR_reject_unallocated_DI_witness','A D witness cannot name a future parameter.'),
        (atomic,'DI',0,[],'SR_reject_case_instead_of_induction','The induction proof needs E(z), not only E(0).'),
        (specialized,'QE',2,-999,'SR_reject_unallocated_Q_target','A Q specialization cannot name a future parameter.')]:
        packet=copy.deepcopy(case['packet'])
        event=next(e for e in case['trace'] if e['rule']==rule)
        packet[event['packet_index']][field]=replacement
        raw(name,packet,meaning)
    return cases


def main():
    import subprocess
    import sys
    cases=build_sr_cases()
    root=Path(__file__).resolve().parent
    destination=root/'sr_certificates.json'
    destination.write_text(json.dumps({'format':'Direct native SR, checked computation insertion',
        'scope':'Untrusted proof producer; complete canonical certificates, not an arithmetic oracle',
        'cases':cases},indent=2)+'\n')
    checker=root.parent/'code/checker_sr_bytes.py'
    results=[]
    for case in cases:
        for optimized in (False,True):
            command=[sys.executable]+(['-O'] if optimized else [])+[str(checker)]
            result=subprocess.run(command,input=json.dumps(case['packet']),text=True,
                                  capture_output=True,timeout=20)
            accepted=result.returncode==0 and result.stdout.strip()=='ACCEPT'
            record={'name':case['name'],'optimized':optimized,
                    'expected':case['accept'],'accepted':accepted,
                    'passed':accepted==case['accept'],
                    'commands':len(case['packet'])-1}
            if not record['passed']:
                record['stderr_tail']=result.stderr[-1600:]
            results.append(record)
    receipt={'status':'passed' if all(r['passed'] for r in results) else 'failed',
             'case_count':len(cases),'accepted_cases':sum(c['accept'] for c in cases),
             'runs':len(results),'results':results}
    (root.parent/'evidence/sr_certificate_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='results'},indent=2))
    for failure in results:
        if not failure['passed']:
            print(json.dumps(failure,indent=2))
    if receipt['status']!='passed':
        raise SystemExit(1)


if __name__=='__main__':
    main()
