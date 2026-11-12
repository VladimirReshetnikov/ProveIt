"""Untrusted explicit proof constructors for deterministic witness discharge.

The selector/parity naming argument is adapted from the pinned incoming
witness_discharge macros. The row order and export instruction are changed:
row 1 names the witness, row 2 transports the supplied equation.
"""
from dataclasses import dataclass

from inherited_reference_kernel import normal as N, opening, map_syntax, replace_parameter
from translate import candidate, selection

H = [0, 0]
ONE = [0, 0]
TWO = [0, ONE]
X, Y, V, U, W = -100001, -100002, -100003, -100004, -100005


def ensure(condition, message='producer mismatch'):
    if not condition:
        raise ValueError(message)


@dataclass
class Theorem:
    goal: object
    proof: object


def S(term):
    return [0, term]


def numeral(n):
    value = 0
    for _ in range(n):
        value = S(value)
    return value


def bind(tree, names):
    names = list(names)
    count = len(names)
    def variable(i, depth):
        if i in names:
            return depth + count - names.index(i)
        return i + count if i > depth else i
    return map_syntax(tree, variable)


def I(counter, seed, variable, body):
    return N([counter, seed, bind(body, [variable])])


def D(body, first=X, second=Y):
    return N([bind(body, [first, second])])


def at(tree, parameter, target):
    return replace_parameter(tree, parameter, target)


def C(counter, zero, positive):
    return I(counter, zero, U, positive)


def parity(counter):
    return I(counter, 0, U, C(U, ONE, 0))


def refl(term):
    term = N(term)
    return Theorem([term, term], ['u', 0, term, None])


def use(index, target, premise, context, scope):
    target = N(target)
    base, body = context[index]
    if base:
        ensure(premise is not None and premise.goal == base, 'wrong clause antecedent')
    result = Theorem(opening(body, target),
                     ['u', index, target, premise.proof if base else None])
    return result


def hypothesis(index, context, scope):
    return use(index, 0, None, context, scope)


def weaken(theorem, ambient_scope, ambient_context, scope_extra=1, context_extra=1):
    def rename(tree):
        if type(tree) is int:
            return tree - scope_extra if tree < -ambient_scope else tree
        return [rename(child) for child in tree]
    def proof(node):
        tag = node[0]
        if tag == 'u':
            index = node[1] + context_extra if node[1] >= ambient_context else node[1]
            return ['u', index, rename(node[2]), proof(node[3]) if node[3] is not None else None]
        if tag == 'i':
            return ['i', rename(node[1]), proof(node[2])]
        if tag == 'e':
            return ['e', rename(node[1]), rename(node[2]), proof(node[3]), proof(node[4])]
        raise ValueError('unknown proof in weakening')
    return Theorem(rename(theorem.goal), proof(theorem.proof))


def introduce(goal, witness, builder, context, scope):
    witness = N(witness)
    body = opening(goal[0], witness, 1)
    fresh = -scope - 1
    eta = fresh if len(body) == 2 and witness == 0 else 0
    assumption = opening(body, eta)
    expected = opening(body, S(fresh))
    branch = builder(fresh, context + [([], assumption)], scope + 1, expected)
    ensure(branch.goal == expected, 'introduction branch differs')
    return Theorem(goal, ['i', witness, branch.proof])


def eliminate(major, builder, context, scope):
    ensure(len(major.goal) == 1, 'major not paired')
    body, base, target, extracted = selection(major.goal[0], scope)
    branch = builder(-scope - 1, context + [(base, body)], scope + 1)
    result = at(branch.goal, -scope - 1, target)
    return Theorem(result, ['e', major.goal[0], branch.goal, major.proof, branch.proof])


def numerical_cases(template, parameter, target, zero_proof, successor_builder, context, scope):
    goal = D(template, W, parameter)
    major = introduce(goal, ONE,
                      lambda z, g, n, expected: successor_builder(z, g, n), context, scope)
    def branch(b, local, level):
        return use(len(context), target,
                   weaken(zero_proof, scope, len(context)), local, level)
    result = eliminate(major, branch, context, scope)
    ensure(result.goal == at(template, parameter, target), 'numerical cases differ')
    return result


def transport(major, minor, template, parameter, context, scope):
    source, target = major.goal
    left, right = minor.goal
    ensure(left == at(template, parameter, source), 'transport source differs')
    hx = at(template, parameter, X)
    matrix = [C(Y, 0, C(parity(Y), hx, X)),
              C(Y, 0, C(parity(Y), right, target))]
    packet = D(matrix)
    def introduction_branch(z, local, level, expected):
        row_template = [C(V, left, source), C(V, right, target)]
        zero = weaken(minor, scope, len(context))
        def successor_builder(zz, extended, next_level):
            return weaken(major, scope, len(context), 2, 2)
        return numerical_cases(row_template, V, parity(S(z)), zero,
                               successor_builder, local, level)
    named = introduce(packet, source, introduction_branch, context, scope)
    def export_branch(b, local, level):
        return use(len(context), TWO, refl(0), local, level)
    result = eliminate(named, export_branch, context, scope)
    ensure(result.goal == [at(template, parameter, target), right], 'transport target differs')
    return result


def symmetry(theorem, context, scope):
    return transport(theorem, refl(theorem.goal[0]), V, V, context, scope)


def congruence(theorem, template, parameter, context, scope):
    return transport(symmetry(theorem, context, scope),
                     refl(at(template, parameter, theorem.goal[1])),
                     template, parameter, context, scope)


def transitivity(first, second, context, scope):
    ensure(first.goal[1] == second.goal[0], 'transitivity middle differs')
    return transport(symmetry(first, context, scope), second, V, V, context, scope)


def equation_transport(equality, theorem, template, parameter, context, scope):
    ensure(theorem.goal == at(template, parameter, equality.goal[0]))
    first = transport(equality, theorem, template[0], parameter, context, scope)
    second = transport(equality, symmetry(first, context, scope), template[1], parameter, context, scope)
    return symmetry(second, context, scope)


def formula_identity(formula, context, scope):
    if len(formula) == 2:
        ensure(formula[0] == formula[1], 'nonreflexive identity')
        return refl(formula[0])
    return introduce(formula, 0,
                     lambda z, g, n, expected: formula_identity(expected, g, n), context, scope)


def implication(antecedent, consequent, builder):
    context = [([], [1, 1])]
    goal = D([C(Y, antecedent[0], consequent[0]), C(Y, antecedent[1], consequent[1])])
    theorem = introduce(goal, ONE,
                        lambda z, g, n, expected: builder(hypothesis(1, g, n), g, n), context, 0)
    return {'goal': theorem.goal, 'proof': theorem.proof}


def alias_zero(context, scope):
    goal = D([C(Y, 0, X), 0])
    return introduce(goal, 0, lambda z, g, n, expected: refl(0), context, scope)


def check_theorem(theorem, context, scope):
    candidate.prove(theorem.goal, theorem.proof, context, scope)
    return theorem
