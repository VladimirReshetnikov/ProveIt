"""Untrusted, checked proof translations between CE5/Eval2 and Horn4.

Both standalone checkers are imported only to validate source and result.
This compiler is not part of either trusted checker-size measurement.
The translations preserve the exact end formula, including open binders.
"""
from copy import deepcopy

import clausal_eval_two as old
import clausal_horn_shared as new


REFLEXIVITY = ([], [1, 1])
TRUTH = [0, 0]


def _proof(proof, old_context, new_context, scope, forward):
    """The new context is the reflexivity clause plus mapped old clauses."""
    def recur(p, g=old_context, h=new_context, n=scope):
        return _proof(p, g, h, n, forward)

    tag = proof[0]
    if tag == 'r':
        return ['u', 0, deepcopy(proof[1]), []]
    if tag == 'v':
        return ['v', recur(proof[1]), recur(proof[2])]
    if tag == 'u':
        index, target, payload = proof[1:]
        if forward:
            premises = [] if not new_context[index + 1][0] else [recur(payload)]
            return ['u', index + 1, deepcopy(target), premises]
        if index == 0:
            return ['r', deepcopy(target)]
        premise = recur(payload[0]) if new_context[index][0] else ['r', 0]
        return ['u', index - 1, deepcopy(target), premise]

    goal, data, branch = proof[1:]
    fresh = -scope - 1
    if tag == 'e':
        source = old if forward else new
        source_context = old_context if forward else new_context
        paired = source.derive(data, source_context, scope)
        body = old.opening(paired[0], fresh, 1)
        antecedent = old.opening(body, 0)
        old_clause = (antecedent, body)
        new_clause = ([antecedent], body)
        out_data = recur(data)
    else:
        body = old.opening(goal[0], data, 1)
        eta = fresh if len(goal[0]) == 2 and data == 0 else 0
        assumption = old.opening(body, eta)
        old_clause = (TRUTH, assumption)
        new_clause = ([], assumption)
        out_data = deepcopy(data)
    out_branch = recur(branch, old_context + [old_clause],
                       new_context + [new_clause], scope + 1)
    return [tag, deepcopy(goal), out_data, out_branch]


def to_horn(certificate):
    """Translate a validated closed CE5/Eval2 certificate to Horn4."""
    old.verify(certificate)
    result = {'goal': deepcopy(certificate['goal']),
              'proof': _proof(certificate['proof'], [], [REFLEXIVITY], 0, True)}
    new.verify(result)
    return result


def from_horn(certificate):
    """Translate a validated closed Horn4 certificate to CE5/Eval2."""
    new.verify(certificate)
    result = {'goal': deepcopy(certificate['goal']),
              'proof': _proof(certificate['proof'], [], [REFLEXIVITY], 0, False)}
    old.verify(result)
    return result
