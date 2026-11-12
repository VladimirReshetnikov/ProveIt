"""Untrusted examples for the mirrored guard. No checker imports this file."""
import copy
import importlib.util
import json
from pathlib import Path
import native_producer as P
import global_producer as G
import normalizer as N

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('inherited_builder',
                                             ROOT / 'reference/inherited_guarded_builder.py')
B = importlib.util.module_from_spec(spec)
# The frozen builder imports its frozen producer. Use its constructors and
# rewrite the derived guard operations below; constructors are plain tuples.
import sys
sys.modules['producer'] = P
spec.loader.exec_module(B)


def guard(index, equation):
    left, right = equation[1:]
    return P.Eq(left, P.C(index, left, right))


def right_expand(proof, computation):
    """a=b, r=b (r syntactically nonzero) |- a=r, without Tr_0."""
    left, endpoint = proof['goal'][1:]
    assert computation['goal'][1] != 0
    assert computation['goal'][2] == endpoint
    if endpoint != 0:
        return N.chain(proof, N.sym(computation))
    if left == 0:
        return N.sym(computation)
    return N.join_zero(proof, computation)


def at_guard(index, proof):
    return right_expand(proof, P.compute(guard(index, proof['goal'])[2]))


def remove_guard(index, proof):
    assert index[0] == 's'
    return N.chain(proof, P.compute(proof['goal'][2]))


def guard_zero(equation):
    return N.sym(P.compute(guard(0, equation)[2]))


def lift_intro(proof, target=None):
    target = target or B.lift_formula(proof['goal'])
    x, y, body = target[1:]
    z = B.fresh('mirror_lift')
    following = P.substitute(P.substitute(body, x, 0), y, P.S(P.V(z)))
    premise = right_expand(proof, P.compute(following[2]))
    return P.introduction(target, 0, z, 'progress', premise)


def lift_elim(proof):
    _, x, y, matrix = proof['goal']
    a = B.fresh('mirror_elim')
    opened = P.substitute(matrix, x, P.V(a))
    base = N.sym(P.compute(P.substitute(opened, y, 0)[2]))
    at1 = P.specialize(P.hyp(P.Q(y, opened)), P.ONE, base)
    answer = N.chain(at1, P.compute(at1['goal'][2]))
    return P.elimination(proof, a, answer)


B.guard = guard
B.at_guard = at_guard
B.remove_guard = remove_guard
B.guard_zero = guard_zero
B.lift_intro = lift_intro
B.lift_elim = lift_elim


def selection(index, left, right):
    assert left[1] == right[1], 'the bootstrap implication needs one left side'
    return P.Eq(left[1], P.C(index, left[2], right[2]))


def selection_wrap(index, left, right, proof):
    return right_expand(proof, P.compute(selection(index, left, right)[2]))


def selection_unwrap(proof):
    return N.chain(proof, P.compute(proof['goal'][2]))


B.selection = selection
B.selection_wrap = selection_wrap
B.selection_unwrap = selection_unwrap


def equation_cases(index, body, base, step_builder, target):
    """Numerical cases through a compound padded matrix; no induction."""
    lifted = B.lift_formula(body)
    at0 = lift_intro(base, P.substitute(lifted, index, 0))
    eigen = B.fresh('equation_case')
    successor = P.S(P.V(eigen))
    at_successor = lift_intro(step_builder(P.V(eigen)),
                              P.substitute(lifted, index, successor))
    result = B.compound_cases(index, lifted, at0, eigen, at_successor, target)
    return lift_elim(result)


def guard_implication(index, equation, base, target):
    """Under the base proof, derive H_y(E(y)) => E(y) by numerical cases."""
    guarded = guard(P.V(index), equation)
    implication = B.implication(guarded, equation)
    guarded0 = P.substitute(guarded, index, 0)
    equation0 = P.substitute(equation, index, 0)
    at0 = B.implication_intro(guarded0, equation0, base,
                              P.substitute(implication, index, 0))
    eigen = B.fresh('guard_case')
    successor = P.S(P.V(eigen))
    guarded_successor = P.substitute(guarded, index, successor)
    equation_successor = P.substitute(equation, index, successor)
    removed = remove_guard(successor, P.hyp(guarded_successor))
    at_successor = B.implication_intro(
        guarded_successor, equation_successor, removed,
        P.substitute(implication, index, successor))
    return B.compound_cases(index, implication, at0, eigen, at_successor, target)


def guarded_induction(index, equation, base, step_builder):
    """Compile arbitrary equation induction to canonical mirrored DI only."""
    witness, eigen = B.fresh('ind_witness'), B.fresh('ind_eigen')
    current = P.V(eigen)
    guarded = guard(P.V(index), equation)
    guarded_current = P.substitute(guarded, index, current)
    equation_current = P.substitute(equation, index, current)
    implication = guard_implication(index, equation, base, current)
    recovered = B.implication_elim(implication, guarded_current,
                                  equation_current, P.hyp(guarded_current))
    next_equation = B.cut(step_builder(current), equation_current, recovered)
    next_guard = at_guard(P.S(current), next_equation)
    return P.introduction(P.D(witness, index, guarded), 0, eigen,
                          'progress', next_guard)


def equation_induction(index, equation, base, step_builder, target):
    major = guarded_induction(index, equation, base, step_builder)
    witness, eigen, guarded = major['goal'][1:]
    opened_witness = B.fresh('ind_open')
    opened = P.substitute(guarded, witness, P.V(opened_witness))
    base_guard = N.sym(P.compute(P.substitute(opened, index, 0)[2]))
    guarded_at_target = P.specialize(P.hyp(P.Q(index, opened)), target,
                                     base_guard)
    implication = guard_implication(index, equation, base, target)
    conclusion = B.implication_elim(
        implication, P.substitute(guarded, index, target),
        P.substitute(equation, index, target), guarded_at_target)
    return P.elimination(major, opened_witness, conclusion)


def lifted_successor(zero_equation):
    """The critical 0=t |- 1=S(t) step, using mirrored guarded DI only."""
    target = zero_equation['goal'][2]
    assert zero_equation['goal'][1] == 0 and target != 0
    state, index = B.fresh('lift_state'), B.fresh('lift_index')
    def iterator(counter):
        return P.I(counter, target, state, P.S(P.V(state)))
    at_zero = P.compute(iterator(0))
    hole = B.fresh('lift_base')
    base = N.tr(N.sym(at_zero), hole, P.Eq(0, P.V(hole)), zero_equation)
    equation = P.Eq(P.V(index), iterator(P.V(index)))
    def step(n):
        hypothesis = P.hyp(P.Eq(n, iterator(n)))
        return N.chain(N.cong(hypothesis, P.S), N.sym(P.compute(iterator(P.S(n)))))
    at_one = equation_induction(index, equation, base, step, P.ONE)
    return N.chain(N.chain(at_one, P.compute(iterator(P.ONE))), N.cong(at_zero, P.S))


B.guarded_induction = guarded_induction
N.numerical_cases = equation_cases
N.lifted_successor = lifted_successor


def audit(proof):
    seen = set()
    seen_formulas = set()
    rows = {'nodes': 0, 'zero_source_transport': 0,
            'atomic_DI': 0, 'compound_DI': 0, 'nonmirrored_atomic_DI': 0,
            'atomic_D_subformulas': 0, 'nonmirrored_atomic_D_subformulas': 0}
    def visit_formula(formula):
        if id(formula) in seen_formulas:
            return
        seen_formulas.add(id(formula))
        if formula[0] == 'q':
            visit_formula(formula[2])
        elif formula[0] == 'd':
            _, x, y, body = formula
            if body[0] == 'eq':
                rows['atomic_D_subformulas'] += 1
                left, right = body[1:]
                mirror = (isinstance(right, tuple) and right[0] == 'i'
                          and right[1] == P.V(y) and right[2] == left)
                if not mirror:
                    rows['nonmirrored_atomic_D_subformulas'] += 1
            visit_formula(body)
    def visit(node):
        if id(node) in seen:
            return
        seen.add(id(node))
        rows['nodes'] += 1
        visit_formula(node['goal'])
        if 'motive' in node:
            visit_formula(node['motive'])
        if node['rule'] == 'Tr' and node['major']['goal'][1] == 0:
            rows['zero_source_transport'] += 1
        if node['rule'] == 'DI':
            _, x, y, body = node['goal']
            if body[0] == 'eq':
                rows['atomic_DI'] += 1
                left, right = body[1:]
                mirror = (isinstance(right, tuple) and right[0] == 'i'
                          and right[1] == P.V(y) and right[2] == left)
                if not mirror:
                    rows['nonmirrored_atomic_DI'] += 1
            else:
                rows['compound_DI'] += 1
        for key in ('major', 'minor', 'premise', 'continuation'):
            if key in node:
                visit(node[key])
    visit(proof)
    return rows


def proof_cases():
    cases = []
    def add(name, proof, expected=True, canonical=True):
        cases.append({'name': name, 'proof': proof, 'expected': expected,
                      'canonical': canonical, 'audit': audit(P.expand_proof(proof))})

    add('zero_computation', P.compute(P.I(0, P.TWO, 'c0_u', P.ONE)))
    add('successor_computation', P.compute(P.I(P.TWO, P.ONE, 'cs_u', P.S(P.V('cs_u')))))
    add('zero_initializer_computation', P.compute(P.I(0, 0, 'cz_u', P.ONE)))
    add('reflexivity_zero', P.reflexivity(0, 'refl_zero'))
    add('reflexivity_two', P.reflexivity(P.TWO, 'refl_two'))
    for label, equation in [('zero', P.Eq(0, 0)), ('two', P.Eq(P.TWO, P.TWO))]:
        proof = P.reflexivity(equation[1], label + '_refl')
        intro = lift_intro(proof)
        add('mirror_DI_' + label, intro)
        add('mirror_DE_' + label, lift_elim(intro))

    x, y, z, u = 'wit_x', 'wit_y', 'wit_z', 'wit_state'
    matrix = P.Eq(P.V(x), P.I(P.V(y), P.V(x), u, P.V(u)))
    current = P.I(P.V(z), P.ONE, u, P.V(u))
    following = P.I(P.S(P.V(z)), P.ONE, u, P.V(u))
    ih = P.hyp(P.Eq(P.ONE, current))
    step = right_expand(ih, P.compute(following))
    add('nonvacuous_witness_progress',
        P.introduction(P.D(x, y, matrix), P.ONE, z, 'progress', step))

    equation = P.Eq(P.TWO, P.TWO)
    implication = B.implication_intro(equation, equation, P.hyp(equation))
    add('compound_case_implication', implication)
    add('compound_implication_elimination',
        B.implication_elim(implication, equation, equation,
                           P.reflexivity(P.TWO, 'imp_minor')))

    index, state = 'ind_n', 'ind_state'
    invariant = P.Eq(P.I(P.V(index), P.ONE, state, P.V(state)), P.ONE)
    base = P.compute(P.I(0, P.ONE, state, P.V(state)))
    def step_builder(n):
        current = P.I(n, P.ONE, state, P.V(state))
        following = P.I(P.S(n), P.ONE, state, P.V(state))
        return N.chain(P.compute(following), P.hyp(P.Eq(current, P.ONE)))
    add('derived_induction_with_used_IH', B.guarded_induction(index, invariant, base, step_builder))

    # A contextual bootstrap where the invariant's left side changes from
    # literal zero at the base to a nonzero variable in the step. This is the
    # obstruction that the orientation of the new guard must overcome.
    premise = P.Eq(0, P.ONE)
    consequence = P.Eq(0, P.TWO)
    shifted = lifted_successor(P.hyp(premise))
    conditional_step = N.chain(P.hyp(premise), shifted)
    add('contextual_zero_source_bootstrap',
        B.implication_intro(premise, consequence, conditional_step))

    box = P.I(0, 0, 'zero_source_box', P.ONE)
    major = P.symmetry(P.compute(box), 'zero_to_box')
    direct = P.transport(major, 'zero_hole', P.Eq(P.V('zero_hole'), 0),
                         P.reflexivity(0, 'zero_minor'))
    add('direct_literal_zero_transport_rejected', direct, expected=False)
    normalized = N.eliminate_zero_sources(direct)
    add('derived_literal_zero_transport', normalized)
    return cases


def packet(proof, global_scope=False):
    emitter = (G if global_scope else P).Emitter()
    return emitter.packet(proof)


def main():
    target = ROOT / 'tests/certificates'
    target.mkdir(exist_ok=True)
    rows = []
    for row in proof_cases():
        proof = row.pop('proof')
        row['files'] = {}
        for scope in ('local', 'global'):
            data = packet(proof, scope == 'global')
            name = row['name'] + '_' + scope + '.json'
            (target / name).write_text(json.dumps(data, separators=(',', ':')) + '\n')
            row['files'][scope] = {'name': name, 'instructions': len(data) - 1}
        rows.append(row)
    (ROOT / 'evidence/cases.json').write_text(json.dumps(rows, indent=2) + '\n')
    print(json.dumps(rows, indent=2))


if __name__ == '__main__':
    main()
