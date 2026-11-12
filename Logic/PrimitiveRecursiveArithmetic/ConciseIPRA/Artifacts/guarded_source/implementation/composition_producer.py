"""Untrusted proof transformation for the combined guarded/source calculus.

The checker never imports this file.  This adapts the pinned source_dispatch
normalizer: numerical case proofs of equations use equation progress with an
unused induction hypothesis, and guarded atomic binders use their true base.
"""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'source_dispatch' / 'tests'))
import normalizer as n

p = n.p
original_transport = n.full_transport


def numerical_cases(index, body, base, step, target):
    if body[0] != 'eq':
        raise ValueError('The reduced bootstrap only uses equation cases')
    closure = p.make_closure(index, body, step, mode='progress',
                             prefix=n.fresh('cases_by_induction'))
    return p.specialize(closure, target, base)


def is_guarded(matrix, index):
    return matrix[0] == 'eq' and all(
        isinstance(term, tuple) and term[0] == 'i'
        and term[1] == p.V(index) and term[2] == 0
        for term in matrix[1:])


def guarded_zero(matrix, index):
    if not is_guarded(matrix, index):
        raise ValueError('Atomic canonical matrices need the literal zero guard')
    base = p.substitute(matrix, index, 0)
    return n.join_zero(p.compute(base[1]), p.compute(base[2]))


def full_transport(major, variable, motive, minor):
    source, target = major['goal'][1:]
    if source != 0 or target == 0 or motive[0] == 'eq':
        return original_transport(major, variable, motive, minor)
    if motive[0] == 'd' and motive[3][0] == 'eq':
        _, witness, index, matrix = motive
        if not is_guarded(matrix, index):
            raise ValueError('No full transport claim for raw atomic D matrices')
        chosen, eigen = n.fresh('guard_witness'), n.fresh('guard_step')
        chosen_matrix = p.substitute(matrix, witness, p.V(chosen))
        source_matrix = p.substitute(chosen_matrix, variable, source)
        source_local = p.Q(index, source_matrix)
        successor = p.S(p.V(eigen))
        source_step = p.specialize(p.hyp(source_local), successor,
                                   guarded_zero(source_matrix, index))
        step_motive = p.substitute(chosen_matrix, index, successor)
        target_step = full_transport(major, variable, step_motive, source_step)
        target_matrix = p.substitute(matrix, variable, target)
        intro = p.introduction(p.D(witness, index, target_matrix),
                               p.V(chosen), eigen, 'progress', target_step)
        return p.elimination(minor, chosen, intro)
    if motive[0] == 'q' and motive[2][0] == 'eq':
        _, index, matrix = motive
        if not is_guarded(matrix, index):
            raise ValueError('No full transport claim for raw atomic Q matrices')
        eigen, unused, elim = (n.fresh('guard_q_step'), n.fresh('guard_q_unused'),
                                n.fresh('guard_q_elim'))
        source_matrix = p.substitute(matrix, variable, source)
        successor = p.S(p.V(eigen))
        source_step = p.specialize(minor, successor,
                                   guarded_zero(source_matrix, index))
        step_motive = p.substitute(matrix, index, successor)
        target_step = full_transport(major, variable, step_motive, source_step)
        target_matrix = p.substitute(matrix, variable, target)
        intro = p.introduction(p.D(unused, index, target_matrix), 0, eigen,
                               'progress', target_step)
        return p.elimination(intro, elim, p.hyp(p.Q(index, target_matrix)))
    # The pinned routine's compound branches recurse through n.full_transport.
    # At a compound matrix its case introduction is still the selected rule.
    return original_transport(major, variable, motive, minor)


n.numerical_cases = numerical_cases
n.full_transport = full_transport


def transform(proof):
    return n.eliminate_zero_sources(proof)


def audit(proof):
    report = n.audit(proof)
    seen, bad_modes = set(), []

    def visit(node):
        if id(node) in seen:
            return
        seen.add(id(node))
        if node['rule'] == 'DI':
            expected = 'progress' if node['goal'][3][0] == 'eq' else 'case'
            if node['mode'] != expected:
                bad_modes.append({'goal': node['goal'], 'mode': node['mode']})
        for field in ('major', 'minor', 'premise', 'continuation'):
            if field in node:
                visit(node[field])

    visit(proof)
    report['wrong_introduction_modes'] = bad_modes
    return report
