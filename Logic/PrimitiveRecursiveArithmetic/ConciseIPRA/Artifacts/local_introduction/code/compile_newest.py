"""Untrusted control-to-newest compiler, checked at every completed call.

Context realizers are proof families indexed by future target extensions.
No completed newest-only proof is weakened by copying its proof tree.
"""
import copy
import diagonal_control as C
import diagonal_newest as N


def rename(tree, mapping):
    if type(tree) is int:
        return mapping[tree] if tree < 0 else tree
    return [rename(child, mapping) for child in tree]


def diagonal(matrix):
    return len(matrix) == 2 and all(
        type(t) is list and len(t) == 3 and t[:2] == [1, 1]
        for t in matrix)


def hypothesis(index):
    return lambda context, scope: ['u', index, None]


def reflexivity(term):
    return lambda context, scope: ['a', term, ['u', len(context), None]]


def use_at(index, term, premise=None):
    def build(context, scope):
        fresh = -scope - 1
        extended = context + [([], [fresh, term])]
        proof = premise(extended, scope + 1) if context[index][0] else None
        return ['a', term, ['u', index, proof]]
    return build


def clause_realizer(index):
    return lambda term, premise: use_at(index, term, premise)


def symmetry(premise, kernel=N):
    def build(context, scope):
        s, t = kernel.derive(premise(context, scope), context, scope)
        fresh = -scope - 1
        extended = context + [([], [fresh, s])]
        major = ['v', [fresh, t], ['u', len(context), None],
                 premise(extended, scope + 1)]
        minor = reflexivity(t)(extended, scope + 1)
        result = ['a', s, ['v', [t, fresh], major, minor]]
        if kernel.derive(result, context, scope) != [t, s]:
            raise AssertionError('symmetry builder')
        return result
    return build


def transport(formula, equality, premise, kernel=N):
    """From s=t and formula(s), build formula(t), under any later extension."""
    def build(context, scope):
        s, t = kernel.derive(equality(context, scope), context, scope)
        if kernel.derive(premise(context, scope), context, scope) != formula(s):
            raise AssertionError('transport source')
        fresh = -scope - 1
        extended = context + [([], [fresh, t])]
        major = ['v', [fresh, s], ['u', len(context), None],
                 symmetry(equality, kernel)(extended, scope + 1)]
        branch = ['v', formula(fresh), major, premise(extended, scope + 1)]
        result = ['a', t, branch]
        if kernel.derive(result, context, scope) != formula(t):
            raise AssertionError('transport result')
        return result
    return build


def compile_proof(proof, source_context=(), source_scope=0,
                  target_context=None, target_scope=None,
                  mapping=None, realizers=None):
    source_context = list(source_context)
    target_context = list(source_context) if target_context is None else list(target_context)
    target_scope = source_scope if target_scope is None else target_scope
    mapping = {n: n for n in range(-source_scope, 0)} if mapping is None else dict(mapping)
    realizers = [clause_realizer(j) for j in range(len(source_context))] if realizers is None else list(realizers)
    expected = rename(C.derive(proof, source_context, source_scope), mapping)
    tag, *args = proof

    def family(subproof):
        return lambda context, scope: compile_proof(
            subproof, source_context, source_scope, context, scope, mapping, realizers)

    if tag == 'c':
        result = [tag] + [rename(a, mapping) for a in args]
    elif tag == 'u':
        index, premise = args
        term = mapping[-source_scope] if source_scope else 0
        base = family(premise) if source_context[index][0] else None
        result = realizers[index](term, base)(target_context, target_scope)
    elif tag == 'v':
        goal, major, minor = args
        source, target = C.derive(major, source_context, source_scope)
        old = mapping[source]
        translated = rename(target, mapping)
        fresh = -target_scope - 1
        extended = target_context + [([], [fresh, old])]
        equality = ['v', [fresh, translated], ['u', len(target_context), None],
                    family(major)(extended, target_scope + 1)]
        new_goal = N.opening(rename(goal, mapping), fresh, old)
        branch = ['v', new_goal, equality, family(minor)(extended, target_scope + 1)]
        result = ['a', old, branch]
    elif tag == 'a':
        term, branch = args
        source_fresh = -source_scope - 1
        target_fresh = -target_scope - 1
        translated = rename(term, mapping)
        sc = source_context + [([], [source_fresh, term])]
        tc = target_context + [([], [target_fresh, translated])]
        result = ['a', translated, compile_proof(
            branch, sc, source_scope + 1, tc, target_scope + 1,
            mapping | {source_fresh: target_fresh},
            realizers + [clause_realizer(len(target_context))])]
    elif tag == 'e':
        goal, major, branch = args
        paired = C.derive(major, source_context, source_scope)
        source_fresh = -source_scope - 1
        target_fresh = -target_scope - 1
        source_body = C.opening(paired[0], source_fresh, 2)
        source_clause = (C.opening(source_body, 0), source_body)
        mapping2 = mapping | {source_fresh: target_fresh}
        target_clause = tuple(rename(part, mapping2) for part in source_clause)
        result = ['e', rename(goal, mapping), family(major)(target_context, target_scope),
                  compile_proof(branch, source_context + [source_clause], source_scope + 1,
                                target_context + [target_clause], target_scope + 1,
                                mapping2, realizers + [clause_realizer(len(target_context))])]
    elif tag == 'i':
        goal, witness, branch = args
        translated_goal = rename(goal, mapping)
        translated_witness = rename(witness, mapping)
        alias = -target_scope - 1
        step = -target_scope - 2
        source_step = -source_scope - 1
        matrix = translated_goal[0]
        eta = step if diagonal(matrix) else 0
        source_eta = source_step if diagonal(goal[0]) else 0
        source_body = C.opening(goal[0], witness, 2)
        source_clause = ([], C.opening(source_body, source_eta))
        alias_context = target_context + [([], [alias, translated_witness])]
        actual_assumption = N.opening(N.opening(matrix, alias, 2), eta)
        branch_context = alias_context + [([], actual_assumption)]
        alias_equality = hypothesis(len(target_context))
        actual_hypothesis = hypothesis(len(alias_context))
        source_hypothesis = transport(
            lambda value: N.opening(N.opening(matrix, value, 2), eta),
            alias_equality, actual_hypothesis)
        realized_clause = lambda term, premise: source_hypothesis
        mapping2 = mapping | {source_step: step}

        def translated_branch(context, scope):
            return compile_proof(branch, source_context + [source_clause], source_scope + 1,
                                 context, scope, mapping2, realizers + [realized_clause])

        repaired = transport(
            lambda value: N.opening(N.opening(matrix, value, 2), [0, step]),
            symmetry(alias_equality), translated_branch)(branch_context, target_scope + 2)
        result = ['a', translated_witness, ['i', translated_goal, repaired]]
    else:
        raise ValueError('source rule')
    if N.derive(result, target_context, target_scope) != expected:
        raise AssertionError(('compiler conclusion', tag))
    return result


def translate(data):
    C.verify(data)
    result = {'goal': copy.deepcopy(data['goal']), 'proof': compile_proof(data['proof'])}
    N.verify(result)
    return result
