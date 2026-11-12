"""Untrusted proof translations for the matched separate-rule control."""
import macros as m
from reference_old import derive, opening, replace_parameter


def control_symmetry(proof, context, scope):
    s, t = derive(proof, context, scope, True)
    return ['t', 1, ['r', s], proof]


def control_formula_transport(equality, proof, template, context, scope):
    s, t = derive(equality, context, scope, True)
    source = opening(template, s)
    target = opening(template, t)
    assert derive(proof, context, scope, True) == source
    if len(template) == 2:
        left, right = template
        first = ['t', left, equality, proof]
        answer = ['t', right, equality, first]
    else:
        witness = -scope - 1
        z = -scope - 2
        source_body = opening(source[0], witness, 1)
        opened_context = context + [(opening(source_body, 0), source_body)]
        target_body = opening(target[0], witness, 1)
        step_context = opened_context + [(m.H, opening(target_body, 0))]
        equality_here = m.weaken(equality, scope, len(context), 2, 2)
        reverse = control_symmetry(equality_here, step_context, scope + 2)
        # Remove the two D coordinates while keeping the external template
        # parameter bound as index1 in the smaller formula templates.
        named_template = opening(template[0], witness, 1)
        base_template = opening(named_template, 0)
        step_template = opening(named_template, m.S(z))
        new_base = m.hypothesis(len(context) + 1)
        old_base = control_formula_transport(reverse, new_base, base_template,
                                             step_context, scope + 2)
        old_step = m.use(len(context), m.S(z), old_base)
        new_step = control_formula_transport(equality_here, old_step, step_template,
                                             step_context, scope + 2)
        introduced = ['i', target, witness, new_step]
        answer = ['e', target, proof, introduced]
    assert derive(answer, context, scope, True) == target
    return answer


def fusion_to_control(proof, context=None, scope=0):
    context = [] if context is None else context
    tag = proof[0]
    if tag == 'r':
        return proof
    if tag == 'u':
        return proof[:3] + [fusion_to_control(proof[3], context, scope)]
    if tag == 'i':
        goal, witness, branch = proof[1:]
        body = opening(goal[0], witness, 1)
        fresh = -scope - 1
        eta = fresh if len(body) == 2 and witness == 0 else 0
        extended = context + [(m.H, opening(body, eta))]
        return proof[:3] + [fusion_to_control(branch, extended, scope + 1)]
    if tag == 'e':
        goal, major, equation, branch = proof[1:]
        paired = derive(major, context, scope)
        fresh = -scope - 1
        body = opening(paired[0], fresh, 1)
        extended = context + [(opening(body, 0), body)]
        old_major = fusion_to_control(major, context, scope)
        old_equation = fusion_to_control(equation, extended, scope + 1)
        old_branch = fusion_to_control(branch, extended, scope + 1)
        formula = derive(branch, extended, scope + 1)
        template = m.bind(formula, [fresh])
        transported = control_formula_transport(old_equation, old_branch, template,
                                                extended, scope + 1)
        answer = ['e', goal, old_major, transported]
        assert derive(answer, context, scope, True) == goal
        return answer
    raise ValueError('fusion rule')


def control_to_fusion(proof, context=None, scope=0):
    context = [] if context is None else context
    tag = proof[0]
    if tag == 'r':
        return proof
    if tag == 'u':
        return proof[:3] + [control_to_fusion(proof[3], context, scope)]
    if tag == 'i':
        goal, witness, branch = proof[1:]
        body = opening(goal[0], witness, 1)
        fresh = -scope - 1
        eta = fresh if len(body) == 2 and witness == 0 else 0
        extended = context + [(m.H, opening(body, eta))]
        return proof[:3] + [control_to_fusion(branch, extended, scope + 1)]
    if tag == 'e':
        goal, major, branch = proof[1:]
        paired = derive(major, context, scope, True)
        fresh = -scope - 1
        body = opening(paired[0], fresh, 1)
        extended = context + [(opening(body, 0), body)]
        return ['e', goal, control_to_fusion(major, context, scope), m.refl(fresh),
                control_to_fusion(branch, extended, scope + 1)]
    if tag == 't':
        template, major, minor = proof[1:]
        first = control_to_fusion(major, context, scope)
        second = control_to_fusion(minor, context, scope)
        return m.crossed_transport(first, second, opening(template, m.V), m.V,
                                   context, scope)
    raise ValueError('control rule')


def control_to_selected(p, context=None, scope=0, unconditional=None):
    context = [] if context is None else context
    unconditional = [] if unconditional is None else unconditional
    tag = p[0]
    if tag == 'r':
        return ['u', 0, p[1], []]
    if tag == 'u':
        j, t, premise = p[1:]
        return ['u', j + 1, t, [] if unconditional[j] else
                control_to_selected(premise, context, scope, unconditional)]
    if tag == 'i':
        goal, witness, branch = p[1:]
        body = opening(goal[0], witness, 1)
        fresh = -scope - 1
        eta = fresh if len(body) == 2 and witness == 0 else 0
        extended = context + [(m.H, opening(body, eta))]
        return ['i', witness, control_to_selected(branch, extended, scope + 1,
                                                 unconditional + [True])]
    if tag == 'e':
        goal, major, branch = p[1:]
        paired = derive(major, context, scope, True)
        body = opening(paired[0], -scope - 1, 1)
        extended = context + [(opening(body, 0), body)]
        return ['e', paired[0], control_to_selected(major, context, scope, unconditional),
                control_to_selected(branch, extended, scope + 1, unconditional + [False])]
    if tag == 't':
        template, major, minor = p[1:]
        s, t = derive(major, context, scope, True)
        return ['t', template, s, t,
                control_to_selected(major, context, scope, unconditional),
                control_to_selected(minor, context, scope, unconditional)]
    raise ValueError('control rule')
