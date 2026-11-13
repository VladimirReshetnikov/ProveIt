"""Untrusted compiler for equation-only aliases and newest specialization.

Recipes are rebuilt in each extended context. No function weakens or rewrites
an already constructed target proof. Positive-depth local transport consumes
its minor as Open's major before it introduces any new parameter.
"""
from dataclasses import dataclass
import copy
import sys
from pathlib import Path
import atomic_alias as K
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'controls'))
import template_source as S


def op(a, value, index=1):
    return K.opening(a, value, index)


def suc(t):
    return [0, t]


def rank(formula):
    return 0 if len(formula) == 2 else 1 + rank(formula[0])


@dataclass
class Recipe:
    formula: object
    build: object

    def proof(self, context, scope):
        return self.build(context, scope)


def hypothesis(index, formula):
    """Ordinary assumptions have a body independent of its binder."""
    return Recipe(formula, lambda context, scope: ['u', index, None])


def computation(counter, seed, body):
    term = [counter, seed, body]
    rhs = seed if counter == 0 else op(body, [counter[1], seed, body])
    return Recipe([term, rhs], lambda context, scope: ['c', counter, seed, body])


def reflexivity(term):
    return Recipe([term, term], lambda context, scope: ['a', term, ['u', len(context), None]])


def symmetry(equality):
    left, right = equality.formula
    def build(context, scope):
        fresh = -scope - 1
        local = context + [([], [fresh, left])]
        hyp = ['u', len(context), None]
        first = ['v', [fresh, right], hyp, equality.proof(local, scope + 1)]
        second = ['v', [right, fresh], first, reflexivity(right).proof(local, scope + 1)]
        return ['a', left, second]
    return Recipe([right, left], build)


def atomic_transport(equality, minor, image):
    """T_0; both premise recipes remain available in alias extensions."""
    left, right = equality.formula
    if minor.formula != image(left) or rank(minor.formula):
        raise ValueError('atomic transport inputs')
    reverse = symmetry(equality)
    def build(context, scope):
        fresh = -scope - 1
        local = context + [([], [fresh, right])]
        alias = ['u', len(context), None]
        b_equals_left = ['v', [fresh, left], alias, reverse.proof(local, scope + 1)]
        branch = ['v', image(fresh), b_equals_left, minor.proof(local, scope + 1)]
        return ['a', right, branch]
    return Recipe(image(right), build)


def name(term):
    # Under D, y=1 and x=2; the iterator's state binder shifts x to3.
    goal = [[[1, term, 3], term]]
    def build(context, scope):
        fresh = -scope - 1
        return ['i', goal, term, ['c', suc(fresh), term, term]]
    return Recipe(goal, build)


def name_equality(index, term, parameter):
    """Uniform b=t from the retained clause opened from Name(t)."""
    body = [[1, term, parameter], term]
    base = computation(0, term, parameter)
    at_one = specialize(index, (base.formula, body), suc(0), base)
    calculate = computation(suc(0), term, parameter)
    return atomic_transport(calculate, at_one, lambda value: [value, term])


def local_compound_transport(equality, minor_proof, image, context, scope):
    """L_k, k>0. The minor is LOCAL and is never put in a later scope."""
    left, right = equality.formula
    source = image(left)
    target = image(right)
    if rank(source) == 0:
        raise ValueError('there is deliberately no local L_0')
    witness = -scope - 1
    source_body = op(source[0], witness, 2)
    source_clause = (op(source_body, 0), source_body)
    opened = context + [source_clause]
    fresh = -scope - 2
    target_body = op(target[0], witness, 2)
    target_base = op(target_body, 0)
    branch_context = opened + [([], target_base)]
    assumption = hypothesis(len(opened), target_base)

    def base_image(value):
        return op(op(image(value)[0], witness, 2), 0)

    def step_image(value):
        return op(op(image(value)[0], witness, 2), suc(fresh))

    moved_base = transport(symmetry(equality), assumption, base_image)
    source_step = specialize(len(context), source_clause, suc(fresh), moved_base)
    moved_step = transport(equality, source_step, step_image)
    branch = moved_step.proof(branch_context, scope + 2)
    introduced = ['i', target, witness, branch]
    return ['e', target, minor_proof, introduced]


def transport(equality, minor, image):
    """Uniform T_k, using local L_k at positive depth."""
    left, right = equality.formula
    if minor.formula != image(left):
        raise ValueError('transport source mismatch')
    if rank(minor.formula) == 0:
        return atomic_transport(equality, minor, image)
    def build(context, scope):
        local_proof = minor.proof(context, scope)
        return local_compound_transport(equality, local_proof, image, context, scope)
    return Recipe(image(right), build)


def specialize(index, clause, term, antecedent=None):
    """Uniform S_k. Clause index is retained across appended extensions."""
    base, body = clause
    result = op(body, term)
    if bool(base) != (antecedent is not None):
        raise ValueError('wrong antecedent convention')
    if base and antecedent.formula != base:
        raise ValueError('specialization antecedent mismatch')
    if rank(body) == 0:
        def atomic(context, scope):
            fresh = -scope - 1
            local = context + [([], [fresh, term])]
            premise = antecedent.proof(local, scope + 1) if base else None
            return ['a', term, ['u', index, premise]]
        return Recipe(result, atomic)

    def compound(context, scope):
        fresh = -scope - 1
        naming = name(term)
        name_body = op(naming.formula[0], fresh, 2)
        name_clause = (op(name_body, 0), name_body)
        local = context + [name_clause]
        eq = name_equality(len(context), term, fresh)
        premise = antecedent.proof(local, scope + 1) if base else None
        local_use = ['u', index, premise]
        moved = local_compound_transport(eq, local_use,
                                        lambda value: op(body, value),
                                        local, scope + 1)
        return ['e', result, naming.proof(context, scope), moved]
    return Recipe(result, compound)


def rename(tree, mapping):
    if type(tree) is int:
        return mapping[tree] if tree < 0 else tree
    return [rename(child, mapping) for child in tree]


def compile_source(proof, source_context=(), source_scope=0,
                   target_context=None, target_scope=None,
                   mapping=None, positions=None):
    """Compile directly at an arbitrary embedding, never weaken target proofs."""
    source_context = list(source_context)
    context = source_context if target_context is None else list(target_context)
    scope = source_scope if target_scope is None else target_scope
    mapping = {i: i for i in range(-source_scope, 0)} if mapping is None else dict(mapping)
    positions = list(range(len(source_context))) if positions is None else list(positions)
    tag, *args = proof

    def recipe(p):
        goal = rename(S.derive(p, source_context, source_scope), mapping)
        return Recipe(goal, lambda c, s: compile_source(
            p, source_context, source_scope, c, s, mapping, positions))

    if tag == 'c':
        return ['c'] + [rename(value, mapping) for value in args]
    if tag == 'u':
        index, term, premise = args
        clause = tuple(rename(value, mapping) for value in source_context[index])
        ant = recipe(premise) if clause[0] else None
        return specialize(positions[index], clause, rename(term, mapping), ant).proof(context, scope)
    if tag == 'x':
        template, major, minor = args
        equality, other = recipe(major), recipe(minor)
        translated = rename(template, mapping)
        rhs = other.formula[1]
        moved = atomic_transport(equality, other,
                                 lambda value: [op(translated, value), rhs])
        return symmetry(moved).proof(context, scope)
    if tag in ('e', 'i'):
        goal, data, branch = args
        old_fresh, new_fresh = -source_scope - 1, -scope - 1
        if tag == 'e':
            paired = S.derive(data, source_context, source_scope)
            body = S.opening(paired[0], old_fresh, 2)
            clause = (S.opening(body, 0), body)
            selected = recipe(data).proof(context, scope)
        else:
            body = S.opening(goal[0], data, 2)
            eta = old_fresh if len(goal[0]) == 2 and data == 0 else 0
            clause = ([], S.opening(body, eta))
            selected = rename(data, mapping)
        extended = mapping | {old_fresh: new_fresh}
        new_clause = tuple(rename(value, extended) for value in clause)
        nested = compile_source(branch, source_context + [clause], source_scope + 1,
                                context + [new_clause], scope + 1,
                                extended, positions + [len(context)])
        return [tag, rename(goal, mapping), selected, nested]
    raise ValueError('unknown source inference')


def translate(data):
    S.verify(data)
    result = {'goal': copy.deepcopy(data['goal']),
              'proof': compile_source(data['proof'])}
    K.verify(result)
    return result
