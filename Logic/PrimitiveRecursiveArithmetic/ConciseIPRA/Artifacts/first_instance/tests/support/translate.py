"""Untrusted translations among old Name, new Name, and matched proof controls."""
from pathlib import Path
import importlib.util
import sys
import reference_old
import reference_kernel as new_reference
import macros as m


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


ROOT = Path(__file__).parent
old_forward = load('old_forward_shared', ROOT / 'old_forward_shared.py')
new_forward = load('new_forward_shared', ROOT / 'new_forward_shared.py')
old_backward = load('old_backward', ROOT / 'old_backward.py')
new_backward = load('new_backward', ROOT / 'new_backward.py')


def forward_to_backward(proof, context=None, scope=0, new=True):
    context = [([], [1, 1])] if context is None else context
    kernel = new_forward if new else old_forward
    goal = kernel.derive(proof, context, scope)
    tag = proof[0]
    if tag == 'u':
        _, j, target, premise = proof
        base, body = context[j]
        return goal, ['u', j, target, forward_to_backward(premise, context, scope, new)[1] if base else None]
    if tag == 'i':
        _, matrix, target, branch = proof
        body = kernel.sub(matrix, target, 1)
        hyp = kernel.sub(body, -scope - 1 if len(body) == 2 and target == 0 else 0)
        return goal, ['i', target, forward_to_backward(branch, context + [([], hyp)], scope + 1, new)[1]]
    if tag == 'e':
        major = proof[1]
        matrix, = kernel.derive(major, context, scope)
        body = kernel.sub(matrix, -scope - 1, 1)
        local = context + [(kernel.sub(body, 0), body)]
        branch = proof[-1]
        result, back_branch = forward_to_backward(branch, local, scope + 1, new)
        back_major = forward_to_backward(major, context, scope, new)[1]
        if new:
            return goal, ['e', matrix, result, back_major, back_branch]
        equation, back_equation = forward_to_backward(proof[2], local, scope + 1, False)
        return goal, ['e', matrix, result, equation[1], back_major, back_equation, back_branch]
    raise ValueError('forward rule')


def backward_to_forward(goal, proof, context=None, scope=0, new=True):
    context = [([], [1, 1])] if context is None else context
    kernel = new_backward if new else old_backward
    kernel.prove(goal, proof, context, scope)
    tag = proof[0]
    if tag == 'u':
        _, j, target, premise = proof
        base, body = context[j]
        return ['u', j, target, backward_to_forward(base, premise, context, scope, new) if base else None]
    if tag == 'i':
        _, target, branch = proof
        body = kernel.sub(goal[0], target, 1)
        hyp = kernel.sub(body, -scope - 1 if len(body) == 2 and target == 0 else 0)
        expected = kernel.sub(body, [0, -scope - 1])
        return ['i', goal[0], target, backward_to_forward(expected, branch, context + [([], hyp)], scope + 1, new)]
    if tag == 'e':
        matrix, result = proof[1:3]
        body = kernel.sub(matrix, -scope - 1, 1)
        local = context + [(kernel.sub(body, 0), body)]
        if new:
            major, branch = proof[3:]
            return ['e', backward_to_forward([matrix], major, context, scope, True), backward_to_forward(result, branch, local, scope + 1, True)]
        target, major, equation, branch = proof[3:]
        return ['e', backward_to_forward([matrix], major, context, scope, False), backward_to_forward([-scope - 1, target], equation, local, scope + 1, False), backward_to_forward(result, branch, local, scope + 1, False)]
    raise ValueError('backward rule')


def control_to_new(proof, context=None, scope=0):
    """Separate ordinary elimination and crossed transport -> deterministic Name."""
    context = [] if context is None else context
    tag = proof[0]
    if tag == 'r':
        return proof
    if tag == 'u':
        return proof[:3] + [control_to_new(proof[3], context, scope)]
    if tag == 'i':
        goal, witness, branch = proof[1:]
        body = reference_old.opening(goal[0], witness, 1)
        fresh = -scope - 1
        eta = fresh if len(body) == 2 and witness == 0 else 0
        extended = context + [(m.H, reference_old.opening(body, eta))]
        return proof[:3] + [control_to_new(branch, extended, scope + 1)]
    if tag == 'e':
        goal, major, branch = proof[1:]
        paired = reference_old.derive(major, context, scope, True)
        body = reference_old.opening(paired[0], -scope - 1, 1)
        extended = context + [(reference_old.opening(body, 0), body)]
        return ['e', goal, control_to_new(major, context, scope), control_to_new(branch, extended, scope + 1)]
    if tag == 't':
        template, major, minor = proof[1:]
        first = control_to_new(major, context, scope)
        second = control_to_new(minor, context, scope)
        return m.crossed_transport(first, second, reference_old.opening(template, m.V), m.V, context, scope)
    raise ValueError('control rule')


def annotated_to_forward(proof, context=None, scope=0, unconditional=None):
    """New rich replay format -> selected forward format, with Refl clause."""
    context = [] if context is None else context
    unconditional = [] if unconditional is None else unconditional
    tag = proof[0]
    if tag == 'r':
        return ['u', 0, proof[1], None]
    if tag == 'u':
        j, target, premise = proof[1:]
        return ['u', j + 1, target, None if unconditional[j] else annotated_to_forward(premise, context, scope, unconditional)]
    if tag == 'i':
        goal, witness, branch = proof[1:]
        body = new_reference.opening(goal[0], witness, 1)
        fresh = -scope - 1
        eta = fresh if len(body) == 2 and witness == 0 else 0
        local = new_reference.opening(body, eta)
        return ['i', goal[0], witness, annotated_to_forward(branch, context + [(m.H, local)], scope + 1, unconditional + [True])]
    if tag == 'e':
        goal, major, branch = proof[1:]
        paired = new_reference.derive(major, context, scope)
        body = new_reference.opening(paired[0], -scope - 1, 1)
        extended = context + [(new_reference.opening(body, 0), body)]
        return ['e', annotated_to_forward(major, context, scope, unconditional), annotated_to_forward(branch, extended, scope + 1, unconditional + [False])]
    raise ValueError('rich rule')


def new_forward_to_old(proof, context=None, scope=0):
    """Expand the implicit equality premise using Refl or the new clause at 1."""
    context = [([], [1, 1])] if context is None else context
    tag = proof[0]
    if tag == 'u':
        j, target, premise = proof[1:]
        base, body = context[j]
        return ['u', j, target, new_forward_to_old(premise, context, scope) if base else None]
    if tag == 'i':
        matrix, target, branch = proof[1:]
        body = new_forward.sub(matrix, target, 1)
        hyp = new_forward.sub(body, -scope - 1 if len(body) == 2 and target == 0 else 0)
        return ['i', matrix, target, new_forward_to_old(branch, context + [([], hyp)], scope + 1)]
    if tag == 'e':
        major, branch = proof[1:]
        matrix, = new_forward.derive(major, context, scope)
        fresh = -scope - 1
        body = new_forward.sub(matrix, fresh, 1)
        base = new_forward.sub(body, 0)
        row = new_forward.sub(body, [0, 0])
        if base == [0, 0] and row[0] == fresh:
            equation = ['u', len(context), [0, 0], ['u', 0, 0, None]]
        else:
            equation = ['u', 0, fresh, None]
        return ['e', new_forward_to_old(major, context, scope), equation, new_forward_to_old(branch, context + [(base, body)], scope + 1)]
    raise ValueError('forward rule')


def forward_to_annotated(proof, context=None, scope=0):
    """Expand a selected proof for the independently implemented replay kernel."""
    context = [([], [1, 1])] if context is None else context
    goal = new_forward.derive(proof, context, scope)
    tag = proof[0]
    if tag == 'u':
        j, target, premise = proof[1:]
        if j == 0:
            return ['r', target]
        base, body = context[j]
        return ['u', j - 1, target, forward_to_annotated(premise, context, scope) if base else ['r', 0]]
    if tag == 'i':
        matrix, target, branch = proof[1:]
        body = new_forward.sub(matrix, target, 1)
        hyp = new_forward.sub(body, -scope - 1 if len(body) == 2 and target == 0 else 0)
        return ['i', goal, target, forward_to_annotated(branch, context + [([], hyp)], scope + 1)]
    if tag == 'e':
        major, branch = proof[1:]
        matrix, = new_forward.derive(major, context, scope)
        body = new_forward.sub(matrix, -scope - 1, 1)
        local = context + [(new_forward.sub(body, 0), body)]
        return ['e', goal, forward_to_annotated(major, context, scope), forward_to_annotated(branch, local, scope + 1)]
    raise ValueError('selected proof')
