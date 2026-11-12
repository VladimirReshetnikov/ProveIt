"""Untrusted finite proof compiler; input and output checkers are independent.

Deleting the root case leaves every formula, clause and scope unchanged.
Root(p:s=t, q:s=r) becomes V0(p, V0(q, Refl(I(0,s;u.0)))).
The reverse translation is inclusion.
"""
import baseline
import reduced


def node_count(proof):
    tag = proof[0]
    if tag == 'r':
        return 1
    if tag in ('u', 'i'):
        return 1 + node_count(proof[3])
    if tag == 'e':
        return 1 + node_count(proof[2]) + node_count(proof[3])
    if tag == 'v':
        return 1 + node_count(proof[1]) + node_count(proof[2])
    raise ValueError('unknown proof tag')


def compile_tree(proof, context, scope):
    """Return the transformed proof and number of deleted root-case nodes."""
    tag = proof[0]
    if tag == 'r':
        return proof, 0
    if tag == 'u':
        branch, count = compile_tree(proof[3], context, scope)
        return ['u', proof[1], proof[2], branch], count
    if tag == 'v':
        first, n = compile_tree(proof[1], context, scope)
        second, m = compile_tree(proof[2], context, scope)
        s, t = baseline.derive(proof[1], context, scope)
        b, r = baseline.derive(proof[2], context, scope)
        if b == s:
            frame = [0, s, 0]
            return ['v', first, ['v', second, ['r', frame]]], n + m + 1
        return ['v', first, second], n + m
    if tag in ('e', 'i'):
        goal, data, branch = proof[1:]
        fresh = -scope - 1
        count = 0
        if tag == 'e':
            paired = baseline.derive(data, context, scope)
            body = baseline.opening(paired[0], fresh, 1)
            clause = (baseline.opening(body, 0), body)
            data, count = compile_tree(data, context, scope)
        else:
            body = baseline.opening(goal[0], data, 1)
            eta = fresh if len(goal[0]) == 2 and data == 0 else 0
            clause = ([0, 0], baseline.opening(body, eta))
        branch, count2 = compile_tree(branch, context + [clause], scope + 1)
        return [tag, goal, data, branch], count + count2
    raise ValueError('unknown proof tag')


def to_reduced(data):
    baseline.verify(data)
    proof, roots = compile_tree(data['proof'], [], 0)
    target = {'goal': data['goal'], 'proof': proof}
    reduced.verify(target)
    if node_count(proof) != node_count(data['proof']) + 2 * roots:
        raise RuntimeError('exact root-replacement node bound failed')
    return target


def to_baseline(data):
    reduced.verify(data)
    baseline.verify(data)
    return data
