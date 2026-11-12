"""Untrusted raw-to-zero-normal compiler, including witness-mode repair.

Both endpoints are independently checked. This is not in the trusted checker.
"""
import baseline
import canonical


def normal(a):
    if type(a) is int:
        return a
    parts = [normal(t) for t in a]
    return parts[1] if len(parts) == 3 and parts[0] == 0 else parts


def refl(a):
    return ['r', a]


def root(p, q, source):
    frame = [[0, 0], source, 1]
    return ['v', p, ['v', q, refl(frame)]]


def symmetry(p, source):
    return root(refl(source), p, source)


def congruence(template, p, source):
    frame = [[0, 0], source, template]
    at_source = ['v', refl(source), refl(frame)]
    at_target = ['v', p, refl(frame)]
    return root(at_target, at_source, frame)


def transport(matrix, p, q, source):
    left, right = matrix
    left_source = canonical.opening(left, source)
    right_source = canonical.opening(right, source)
    across_left = root(congruence(left, p, source), q, left_source)
    return root(congruence(right, p, source), across_left, right_source)


def replace_assumption(proof, index, replacement):
    tag = proof[0]
    if tag == 'r':
        return proof
    if tag == 'u':
        if proof[1] == index:
            return replacement
        return ['u', proof[1], proof[2],
                replace_assumption(proof[3], index, replacement)]
    if tag == 'v':
        return ['v', replace_assumption(proof[1], index, replacement),
                replace_assumption(proof[2], index, replacement)]
    if tag == 'e':
        return ['e', proof[1],
                replace_assumption(proof[2], index, replacement),
                replace_assumption(proof[3], index, replacement)]
    if tag == 'i':
        return ['i', proof[1], proof[2],
                replace_assumption(proof[3], index, replacement)]
    raise ValueError('unknown proof instruction')


def compile_tree(proof, context, scope, counts):
    tag = proof[0]
    if tag == 'r':
        return refl(normal(proof[1]))
    if tag == 'u':
        return ['u', proof[1], normal(proof[2]),
                compile_tree(proof[3], context, scope, counts)]
    if tag == 'v':
        p = compile_tree(proof[1], context, scope, counts)
        q = compile_tree(proof[2], context, scope, counts)
        s, _ = baseline.derive(proof[1], context, scope)
        b, _ = baseline.derive(proof[2], context, scope)
        if b == s or b[0] == 0:
            counts['root_or_zero_expansions'] += 1
            return root(p, q, normal(s))
        return ['v', p, q]
    goal, data, branch = proof[1:]
    fresh = -scope - 1
    if tag == 'e':
        paired = baseline.derive(data, context, scope)
        body = baseline.opening(paired[0], fresh, 1)
        clause = (baseline.opening(body, 0), body)
        return ['e', normal(goal), compile_tree(data, context, scope, counts),
                compile_tree(branch, context + [clause], scope + 1, counts)]
    if tag == 'i':
        body = baseline.opening(goal[0], data, 1)
        eta = fresh if len(goal[0]) == 2 and data == 0 else 0
        clause = ([0, 0], baseline.opening(body, eta))
        compiled = compile_tree(branch, context + [clause], scope + 1, counts)
        witness = normal(data)
        matrix = normal(goal[0])
        if len(matrix) == 2 and data != 0 and witness == 0:
            counts['witness_mode_repairs'] += 1
            alias = [[0, 0], 0, 0]
            alias_zero = ['v', refl(0), refl(alias)]
            assumed = ['u', len(context), 0, refl(0)]
            base_template = canonical.opening(matrix, 0)
            old_base = transport(base_template, alias_zero, assumed, alias)
            compiled = replace_assumption(compiled, len(context), old_base)
            step_template = canonical.opening(matrix, [0, fresh])
            compiled = transport(step_template, symmetry(alias_zero, alias),
                                 compiled, 0)
            witness = alias
        return ['i', normal(goal), witness, compiled]
    raise ValueError('unknown proof instruction')


def to_canonical(data):
    baseline.verify(data)
    counts = {'root_or_zero_expansions': 0, 'witness_mode_repairs': 0}
    target = {'goal': normal(data['goal']),
              'proof': compile_tree(data['proof'], [], 0, counts)}
    canonical.verify(target)
    return target, counts
