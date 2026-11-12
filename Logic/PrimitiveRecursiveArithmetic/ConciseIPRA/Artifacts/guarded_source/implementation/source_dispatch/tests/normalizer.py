"""Untrusted native proof construction exercising zero-source admissibility.

Every primitive Tr produced here has a syntactically nonzero source.  The
compiler independently emits packets for the reduced source-dispatch kernel.
"""
import itertools
import native_producer as p

serial = itertools.count()

def fresh(prefix):
    return prefix + '_' + str(next(serial))

def tr(major, variable, motive, minor):
    assert major['goal'][1] != 0, 'forbidden zero-source primitive transport'
    return p.transport(major, variable, motive, minor)

def sym(proof):
    assert proof['goal'][1] != 0
    return p.symmetry(proof, fresh('sym'))

def chain(first, second):
    assert first['goal'][2] == second['goal'][1]
    assert second['goal'][1] != 0
    return p.transitivity(first, second, fresh('join'))

def cong(proof, function):
    assert proof['goal'][1] != 0
    return p.congruence(proof, function, fresh('cong'))

def box(term):
    return p.I(0, term, '_unused_box_state', 0)

def join_zero(first, second):
    """From nonzero-source r=0 and s=0, derive r=s without Tr_0."""
    assert first['goal'][2] == second['goal'][2] == 0
    zero_box = box(0)
    def to_box(proof):
        source = proof['goal'][1]
        assert source != 0
        source_box = box(source)
        hole = fresh('zero_join_hole')
        zero_box_to_source_box = tr(proof, hole, p.Eq(box(p.V(hole)), source_box),
                                    p.reflexivity(source_box, fresh('ref')))
        source_box_to_zero_box = sym(zero_box_to_source_box)
        hole = fresh('zero_join_unbox')
        return tr(p.compute(source_box), hole, p.Eq(p.V(hole), zero_box),
                  source_box_to_zero_box)
    first_to_box, second_to_box = to_box(first), to_box(second)
    return chain(first_to_box, sym(second_to_box))

def lifted_successor(zero_equation):
    """Under 0=t, t syntactically nonzero, derive 1=S(t) by equation induction."""
    _, zero, target = zero_equation['goal']
    assert zero == 0 and target != 0
    state, n = fresh('lift_state'), fresh('lift_n')
    def iterator(counter):
        return p.I(counter, target, state, p.S(p.V(state)))
    at_zero = p.compute(iterator(0))
    hole = fresh('lift_base')
    base = tr(sym(at_zero), hole, p.Eq(0, p.V(hole)), zero_equation)
    body = p.Eq(p.V(n), iterator(p.V(n)))
    def step(k):
        ih = p.hyp(p.Eq(k, iterator(k)))
        return chain(cong(ih, p.S), sym(p.compute(iterator(p.S(k)))))
    closure = p.make_closure(n, body, step, prefix=fresh('lift_closure'))
    at_one = p.specialize(closure, p.ONE, base)
    return chain(chain(at_one, p.compute(iterator(p.ONE))), cong(at_zero, p.S))

def parity(counter):
    return p.I(counter, 0, '_parity_state', p.C(p.V('_parity_state'), p.ONE, 0))

def parity_endpoints():
    """Produce P(1)=1 and P(2)=0 by forward computation only."""
    p0 = p.compute(parity(0))
    p1 = chain(chain(p.compute(parity(p.ONE)),
                     cong(p0, lambda u: p.C(u, p.ONE, 0))),
               p.compute(p.C(0, p.ONE, 0)))
    p2 = chain(chain(p.compute(parity(p.TWO)),
                     cong(p1, lambda u: p.C(u, p.ONE, 0))),
               p.compute(p.C(p.ONE, p.ONE, 0)))
    return p1, p2

def zero_one_symmetry(zero_equation):
    """Explicit special case 0=1 |- 1=0 of the general written lemma."""
    assert zero_equation['goal'] == p.Eq(0, p.ONE)
    shifted = lifted_successor(zero_equation)  # 1=2
    parity_equation = cong(shifted, parity)
    p1, p2 = parity_endpoints()
    hole = fresh('parity_left')
    one_to_p2 = tr(p1, hole, p.Eq(p.V(hole), parity(p.TWO)), parity_equation)
    hole = fresh('parity_right')
    return tr(p2, hole, p.Eq(p.ONE, p.V(hole)), one_to_p2)

def symmetry_fixture():
    """Closed conditional symmetry: D_{u,y}(C(y,0,1)=C(y,1,0))."""
    y, witness, eigen = fresh('case_y'), fresh('unused'), fresh('case_z')
    def left(n): return p.C(n, 0, p.ONE)
    def right(n): return p.C(n, p.ONE, 0)
    matrix = p.Eq(left(p.V(y)), right(p.V(y)))
    zero_hyp = p.hyp(p.Eq(left(0), right(0)))
    hole = fresh('extract_left')
    zero_to_right = tr(p.compute(left(0)), hole, p.Eq(p.V(hole), right(0)), zero_hyp)
    hole = fresh('extract_right')
    zero_to_one = tr(p.compute(right(0)), hole, p.Eq(0, p.V(hole)), zero_to_right)
    one_to_zero = zero_one_symmetry(zero_to_one)
    successor = p.S(p.V(eigen))
    hole = fresh('lift_left')
    left_to_zero = tr(sym(p.compute(left(successor))), hole, p.Eq(p.V(hole), 0), one_to_zero)
    conclusion = join_zero(left_to_zero, p.compute(right(successor)))
    return p.introduction(p.D(witness, y, matrix), 0, eigen, 'case', conclusion)

def numerical_cases(index, body, base, step, target):
    closure = p.make_closure(index, body, step, mode='case', prefix=fresh('cases'))
    return p.specialize(closure, target, base)

def zero_test(value): return p.C(value, p.ONE, 0)
def positive_test(value): return p.C(value, 0, p.ONE)
def plateau_step(value): return p.C(value, p.ONE, p.TWO)
def plateau(counter): return p.I(counter, 0, '_plateau_state', plateau_step(p.V('_plateau_state')))
def singleton(counter): return parity(plateau(counter))

def join_at_nonzero(first, second):
    assert first['goal'][2] == second['goal'][2] != 0
    return chain(first, sym(second))

def positive_plateau_step(target):
    n = fresh('positive_n')
    body = p.Eq(plateau_step(p.V(n)), p.S(positive_test(p.V(n))))
    base = join_at_nonzero(p.compute(plateau_step(0)), cong(p.compute(positive_test(0)), p.S))
    def step(k):
        return join_at_nonzero(p.compute(plateau_step(p.S(k))),
                               cong(p.compute(positive_test(p.S(k))), p.S))
    return numerical_cases(n, body, base, step, target)

def plateau_one():
    return chain(chain(p.compute(plateau(p.ONE)),
                       cong(p.compute(plateau(0)), plateau_step)),
                 p.compute(plateau_step(0)))

def plateau_twice(target):
    once = chain(p.compute(plateau(p.S(target))), positive_plateau_step(plateau(target)))
    return chain(chain(p.compute(plateau(p.S(p.S(target)))), cong(once, plateau_step)),
                 p.compute(plateau_step(p.S(positive_test(plateau(target))))))

def singleton_one():
    return chain(cong(plateau_one(), parity), parity_endpoints()[0])

def singleton_twice(target):
    return chain(cong(plateau_twice(target), parity), parity_endpoints()[1])

def singleton_successor(target):
    n = fresh('singleton_n')
    body = p.Eq(singleton(p.S(p.V(n))), zero_test(p.V(n)))
    base = join_at_nonzero(singleton_one(), p.compute(zero_test(0)))
    def step(k):
        return join_zero(singleton_twice(k), p.compute(zero_test(p.S(k))))
    return numerical_cases(n, body, base, step, target)

def zero_filter(target):
    n = fresh('filter_n')
    def filtered(value): return p.C(zero_test(value), value, 0)
    body = p.Eq(p.V(n), filtered(p.V(n)))
    base_reverse = chain(cong(p.compute(zero_test(0)), lambda z: p.C(z, 0, 0)),
                         p.compute(p.C(p.ONE, 0, 0)))
    base = sym(base_reverse)
    def step(k):
        value = p.S(k)
        reverse = chain(cong(p.compute(zero_test(value)), lambda z: p.C(z, value, 0)),
                        p.compute(p.C(0, value, 0)))
        return sym(reverse)
    return numerical_cases(n, body, base, step, target)

def zero_symmetry(zero_equation):
    """Uniform native derivation of 0=t |- t=0 with only permitted Tr sources."""
    assert zero_equation['goal'][1] == 0
    target = zero_equation['goal'][2]
    if target == 0: return p.reflexivity(0, fresh('trivial_zero'))
    shifted = lifted_successor(zero_equation)
    at_singletons = cong(shifted, singleton)
    hole = fresh('singleton_left')
    one_to_singleton = tr(singleton_one(), hole,
                          p.Eq(p.V(hole), singleton(p.S(target))), at_singletons)
    hole = fresh('singleton_right')
    one_to_test = tr(singleton_successor(target), hole,
                     p.Eq(p.ONE, p.V(hole)), one_to_singleton)
    test_to_one = sym(one_to_test)
    hole = fresh('filter_change')
    changed = tr(test_to_one, hole, p.Eq(target, p.C(p.V(hole), target, 0)), zero_filter(target))
    return chain(changed, p.compute(p.C(p.ONE, target, 0)))

def full_symmetry(proof):
    return zero_symmetry(proof) if proof['goal'][1] == 0 else sym(proof)

def full_chain(first, second):
    _, source, middle = first['goal']
    _, other_middle, target = second['goal']
    assert middle == other_middle
    if middle != 0: return chain(first, second)
    if source == 0: return second
    if target == 0: return first
    return join_zero(first, full_symmetry(second))

def full_congruence(proof, variable, template):
    source, target = proof['goal'][1:]
    source_image = p.substitute(template, variable, source)
    target_image = p.substitute(template, variable, target)
    if source_image == target_image:
        return p.reflexivity(source_image, fresh('constant_congruence'))
    if template == p.V(variable): return proof
    def function(value): return p.substitute(template, variable, value)
    if source != 0: return cong(proof, function)
    return full_symmetry(cong(zero_symmetry(proof), function))

def full_transport(major, variable, motive, minor):
    source, target = major['goal'][1:]
    assert minor['goal'] == p.substitute(motive, variable, source)
    if source != 0: return tr(major, variable, motive, minor)
    if target == 0: return minor
    tag = motive[0]
    if tag == 'eq':
        left = full_congruence(major, variable, motive[1])
        right = full_congruence(major, variable, motive[2])
        return full_chain(full_chain(full_symmetry(left), minor), right)
    if tag == 'q':
        _, index, matrix = motive
        eigen, unused, elim = fresh('q_step'), fresh('q_unused'), fresh('q_elim')
        target_matrix = p.substitute(matrix, variable, target)
        target_base = p.substitute(target_matrix, index, 0)
        base_motive = p.substitute(matrix, index, 0)
        source_base = full_transport(full_symmetry(major), variable, base_motive, p.hyp(target_base))
        source_step = p.specialize(minor, p.S(p.V(eigen)), source_base)
        step_motive = p.substitute(matrix, index, p.S(p.V(eigen)))
        target_step = full_transport(major, variable, step_motive, source_step)
        paired = p.D(unused, index, target_matrix)
        introduction = p.introduction(paired, 0, eigen, 'case', target_step)
        return p.elimination(introduction, elim, p.hyp(p.Q(index, target_matrix)))
    if tag == 'd':
        _, witness, index, matrix = motive
        chosen, eigen = fresh('d_witness'), fresh('d_step')
        source_matrix = p.substitute(matrix, variable, source)
        target_matrix = p.substitute(matrix, variable, target)
        source_local = p.Q(index, p.substitute(source_matrix, witness, p.V(chosen)))
        chosen_motive = p.substitute(matrix, witness, p.V(chosen))
        base_motive = p.substitute(chosen_motive, index, 0)
        target_base = p.substitute(base_motive, variable, target)
        source_base = full_transport(full_symmetry(major), variable, base_motive, p.hyp(target_base))
        source_step = p.specialize(p.hyp(source_local), p.S(p.V(eigen)), source_base)
        step_motive = p.substitute(chosen_motive, index, p.S(p.V(eigen)))
        target_step = full_transport(major, variable, step_motive, source_step)
        introduction = p.introduction(p.D(witness, index, target_matrix), p.V(chosen), eigen, 'case', target_step)
        return p.elimination(minor, chosen, introduction)
    raise ValueError(tag)

def eliminate_zero_sources(proof, memo=None):
    if memo is None: memo = {}
    if id(proof) in memo: return memo[id(proof)]
    result = dict(proof)
    for field in ('major', 'minor', 'premise', 'continuation'):
        if field in result: result[field] = eliminate_zero_sources(result[field], memo)
    if result['rule'] == 'Tr' and result['major']['goal'][1] == 0:
        result = full_transport(result['major'], result['variable'], result['motive'], result['minor'])
    memo[id(proof)] = result
    return result

def audit(proof):
    seen, nodes, zero_sources = set(), 0, []
    def visit(node):
        nonlocal nodes
        if id(node) in seen: return
        seen.add(id(node)); nodes += 1
        if node['rule'] == 'Tr' and node['major']['goal'][1] == 0:
            zero_sources.append(node['goal'])
        for field in ('major', 'minor', 'premise', 'continuation'):
            if field in node: visit(node[field])
    visit(proof)
    return {'distinct_proof_nodes': nodes, 'forbidden_zero_sources': zero_sources}

