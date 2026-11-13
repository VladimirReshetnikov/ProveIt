"""Untrusted compiler A_* -> A_nu^=, implementing persistent proof families.

Every returned derivation is checked by the small standalone target checker.
Families are Python functions that rebuild a proof in a later world; no finished
target derivation is copied into a larger scope. The binder-depth recursion in
transport is the new construction. The source compiler is structurally recursive.

Adapted from the pinned local_introduction/compile_newest.py (MIT-0).
"""
import copy
import json
import sys
import source_liberal as C
import equation_back as N


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


def symmetry(premise):
    def build(context, scope):
        s, t = N.derive(premise(context, scope), context, scope)
        fresh = -scope - 1
        extended = context + [([], [fresh, s])]
        major = ['v', [fresh, t], ['u', len(context), None],
                 premise(extended, scope + 1)]
        minor = reflexivity(t)(extended, scope + 1)
        result = ['a', s, ['v', [t, fresh], major, minor]]
        if N.derive(result, context, scope) != [t, s]:
            raise AssertionError('symmetry builder')
        return result
    return build


def diagonal_zero_row(matrix, witness):
    """Persistent proof of B(witness,0), using I0 and atomic transport only."""
    if not diagonal(matrix):
        raise ValueError('diagonal matrix required')
    row = N.opening(N.opening(matrix, witness, 2), 0)
    left, right = row
    if left[:2] != [0, 0] or right[:2] != [0, 0]:
        raise AssertionError('diagonal zero row')
    left_zero = lambda context, scope: ['c', *left]
    right_zero = lambda context, scope: ['c', *right]
    return transport(lambda value: [left, value], symmetry(right_zero), left_zero)


def transport(formula, equality, premise):
    """From persistent s=t and F(s), rebuild a persistent proof of F(t).

    The recursive calls in the D case concern its matrix, one binder smaller.
    Atomic transport uses exactly two atomic Back steps in one fresh Alias.
    """
    def build(context, scope):
        s, t = N.derive(equality(context, scope), context, scope)
        source = formula(s)
        target = formula(t)
        proof = premise(context, scope)
        if N.derive(proof, context, scope) != source:
            raise AssertionError('transport source')
        fresh = -scope - 1
        if len(target) == 2:
            extended = context + [([], [fresh, t])]
            major = ['v', [fresh, s], ['u', len(context), None],
                     symmetry(equality)(extended, scope + 1)]
            branch = ['v', formula(fresh), major, premise(extended, scope + 1)]
            result = ['a', t, branch]
        else:
            if len(source) != 1 or len(target) != 1:
                raise AssertionError('formula shape')
            # Open the source at b, then Close the target at that same newest b.
            b = fresh
            z = fresh - 1
            opened = N.opening(source[0], b, 2)
            clause = (N.opening(opened, 0), opened)
            opened_context = context + [clause]
            target_body = N.opening(target[0], b, 2)
            eta = z if diagonal(target[0]) else 0
            assumption = N.opening(target_body, eta)
            step_context = opened_context + [([], assumption)]
            if diagonal(target[0]):
                target_zero = diagonal_zero_row(target[0], b)
            else:
                target_zero = hypothesis(len(opened_context))
            zero_template = lambda value: N.opening(
                N.opening(formula(value)[0], b, 2), 0)
            source_zero = transport(zero_template, symmetry(equality), target_zero)
            source_step = use_at(len(context), [0, z], source_zero)
            step_template = lambda value: N.opening(
                N.opening(formula(value)[0], b, 2), [0, z])
            target_step = transport(step_template, equality, source_step)
            close = ['i', target, target_step(step_context, scope + 2)]
            result = ['e', target, proof, close]
        if N.derive(result, context, scope) != target:
            raise AssertionError('transport result')
        return result
    return build


def compile_proof(proof, source_context=(), source_scope=0,
                  target_context=None, target_scope=None,
                  mapping=None, realizers=None):
    """Compile one liberal proof, with realized rather than copied assumptions."""
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
        index, term, premise = args
        translated_term = rename(term, mapping)
        base = family(premise) if source_context[index][0] else None
        result = realizers[index](translated_term, base)(target_context, target_scope)
    elif tag == 'v':
        goal, major, minor = args
        source, target = C.derive(major, source_context, source_scope)
        old = mapping[source]
        translated_goal = rename(goal, mapping)
        template = lambda value: N.opening(translated_goal, value, old)
        result = transport(template, symmetry(family(major)), family(minor))(
            target_context, target_scope)
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


def expand_legacy(proof, scope=0, deterministic=False):
    """Convert a pinned fixture to A_*; this changes only certificate fields."""
    tag, *args = proof
    if tag == 'c':
        return proof
    if tag == 'u':
        index, premise = args
        return [tag, index, -scope, expand_legacy(premise, scope, deterministic)
                if premise is not None else None]
    if tag == 'v':
        goal, major, minor = args
        return [tag, goal, expand_legacy(major, scope, deterministic),
                expand_legacy(minor, scope, deterministic)]
    if tag == 'a':
        term, branch = args
        return [tag, term, expand_legacy(branch, scope + 1, deterministic)]
    if tag == 'e':
        goal, major, branch = args
        return [tag, goal, expand_legacy(major, scope, deterministic),
                expand_legacy(branch, scope + 1, deterministic)]
    if tag == 'i':
        if deterministic:
            goal, branch = args
            witness = -scope
        else:
            goal, witness, branch = args
        return [tag, goal, witness, expand_legacy(branch, scope + 1, deterministic)]
    raise ValueError('legacy source rule')


if __name__ == '__main__':
    json.dump(translate(json.load(sys.stdin)), sys.stdout, separators=(',', ':'))
    print()
