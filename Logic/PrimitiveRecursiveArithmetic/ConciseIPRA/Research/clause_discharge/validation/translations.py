"""Untrusted translations for deterministic fixed-witness discharge.

The explicit reference proof language has separate equality transport.
Its inherited replay engine is independent of the selected acceptance file.
"""
import macros as m
import control_translations as ct
from reference_kernel import derive, opening, replace_parameter


def automatic(proof, context=None, scope=0, unconditional=None):
    """Export a packet-built reference proof to the new three-rule format."""
    context = [] if context is None else context
    unconditional = [] if unconditional is None else unconditional
    tag = proof[0]
    if tag == 'r':
        return ['u', 0, proof[1], None]
    if tag == 'u':
        j, t, premise = proof[1:]
        return ['u', j + 1, t, None if unconditional[j] else
                automatic(premise, context, scope, unconditional)]
    if tag == 'i':
        goal, witness, branch = proof[1:]
        body = opening(goal[0], witness, 1)
        fresh = -scope - 1
        eta = fresh if len(body) == 2 and witness == 0 else 0
        local = context + [(m.H, opening(body, eta))]
        return ['i', witness, automatic(branch, local, scope + 1,
                                        unconditional + [True])]
    if tag == 'e':
        goal, major, equality, branch = proof[1:]
        paired = derive(major, context, scope)
        fresh = -scope - 1
        body = opening(paired[0], fresh, 1)
        base = opening(body, 0)
        local = context + [(base, body)]
        formula = derive(branch, local, scope + 1)
        s, t = opening(body, m.ONE) if base == m.H else (0, 0)
        result = replace_parameter(formula, fresh, t) if s == fresh else formula
        if result != goal:
            raise ValueError('reference proof is not a deterministic packet')
        return ['e', paired[0], formula,
                automatic(major, context, scope, unconditional),
                automatic(branch, local, scope + 1, unconditional + [False])]
    raise ValueError('unknown reference instruction')


def to_control(goal, proof, context=None):
    """Every selected proof becomes a separate-rule control proof."""
    context = [([], [1, 1])] if context is None else context
    scope = len(context) - 1
    ref_context = [(base or m.H, body) for base, body in context[1:]]
    tag = proof[0]
    if tag == 'u':
        j, t, premise = proof[1:]
        if j == 0:
            return ['r', t]
        base, body = context[j]
        return ['u', j - 1, t, to_control(base, premise, context) if base else ['r', 0]]
    if tag == 'i':
        witness, branch = proof[1:]
        body = opening(goal[0], witness, 1)
        fresh = -scope - 1
        eta = fresh if len(body) == 2 and witness == 0 else 0
        local = context + [([], opening(body, eta))]
        step = to_control(opening(body, [0, fresh]), branch, local)
        return ['i', goal, witness, step]
    if tag == 'e':
        matrix, formula, major, branch = proof[1:]
        fresh = -scope - 1
        body = opening(matrix, fresh, 1)
        base = opening(body, 0)
        local = context + [(base, body)]
        target_context = ref_context + [(base, body)]
        major_control = to_control([matrix], major, context)
        branch_control = to_control(formula, branch, local)
        s, t = opening(body, m.ONE) if base == m.H else (0, 0)
        if s == fresh:
            equality = ['u', len(ref_context), m.ONE, ['r', 0]]
            branch_control = ct.control_formula_transport(
                equality, branch_control, m.bind(formula, [fresh]),
                target_context, scope + 1)
        result = ['e', goal, major_control, branch_control]
        if derive(result, ref_context, scope, True) != goal:
            raise ValueError('reverse translation changed the goal')
        return result
    raise ValueError('unknown selected instruction')


def from_control(proof, context=None, scope=0):
    """Compile all separate equality steps using the swapped-row packet."""
    fusion = ct.control_to_fusion(proof, context, scope)
    return automatic(fusion, context, scope)
