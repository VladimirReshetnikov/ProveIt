"""Eliminate the identity case of raw CE5 Eval.

This is an untrusted proof producer. Both complete checkers validate every
public input and output. Zero-frame construction preserves end formulas.
"""
import clausal_eval as baseline
import clausal_eval_two as two


def transform(proof, context, scope):
    tag = proof[0]
    if tag == 'r':
        return proof
    if tag == 'u':
        return ['u', proof[1], proof[2], transform(proof[3], context, scope)]
    if tag == 'v':
        s, t = baseline.derive(proof[1], context, scope)
        b, r = baseline.derive(proof[2], context, scope)
        p = transform(proof[1], context, scope)
        q = transform(proof[2], context, scope)
        if b == s:
            frame = [0, s, 1]
            return ['v', p, ['v', q, ['r', frame]]]
        return ['v', p, q]
    goal, data, branch = proof[1:]
    fresh = -scope - 1
    if tag == 'e':
        paired = baseline.derive(data, context, scope)
        body = baseline.opening(paired[0], fresh, 1)
        clause = (baseline.opening(body, 0), body)
        data = transform(data, context, scope)
    else:
        body = baseline.opening(goal[0], data, 1)
        eta = fresh if len(goal[0]) == 2 and data == 0 else 0
        clause = ([0, 0], baseline.opening(body, eta))
    return [tag, goal, data, transform(branch, context + [clause], scope + 1)]


def to_two(certificate):
    baseline.verify(certificate)
    output = {'goal': certificate['goal'],
              'proof': transform(certificate['proof'], [], 0)}
    two.verify(output)
    return output


def from_two(certificate):
    two.verify(certificate)
    baseline.verify(certificate)
    return certificate
