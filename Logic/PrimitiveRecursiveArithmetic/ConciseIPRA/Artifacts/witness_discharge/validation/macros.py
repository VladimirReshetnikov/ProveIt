"""Untrusted explicit proof constructors for the arity-coded fusion calculus."""
from copy import deepcopy
from reference_kernel import normal as N, opening, map_syntax, replace_parameter
from reference_kernel import derive


H = [0, 0]
ONE = [0, 0]
TWO = [0, ONE]
X, Y, V, U, W = -100001, -100002, -100003, -100004, -100005


def S(t):
    return [0, t]


def numeral(n):
    a = 0
    for _ in range(n):
        a = S(a)
    return a


def bind(a, names):
    names = list(names)
    amount = len(names)
    def variable(i, d):
        if i in names:
            return d + amount - names.index(i)
        return i + amount if i > d else i
    return map_syntax(a, variable)


def I(counter, seed, parameter, body):
    return N([counter, seed, bind(body, [parameter])])


def D(body, first=X, second=Y):
    return N([bind(body, [first, second])])


def at(a, parameter, target):
    return replace_parameter(a, parameter, target)


def C(control, zero, successor):
    return I(control, zero, U, successor)


def parity(a):
    return I(a, 0, U, C(U, ONE, 0))


def refl(t):
    return ['r', N(t)]


def use(index, target, premise):
    return ['u', index, N(target), premise]


def hypothesis(index):
    return use(index, 0, refl(0))


def weaken(p, ambient_scope, ambient_context, scope_extra=1, context_extra=1):
    """Insert unused free parameters/context clauses before local ones.

    Old ambient variables and context references are unchanged.  Local
    eigenlevels and locally introduced clause indices move past the insert.
    """
    def rename(a):
        if type(a) is int:
            return a - scope_extra if a < -ambient_scope else a
        return [rename(x) for x in a]
    tag = p[0]
    if tag == 'r':
        return ['r', rename(p[1])]
    if tag == 'u':
        j = p[1] + context_extra if p[1] >= ambient_context else p[1]
        return ['u', j, rename(p[2]), weaken(p[3], ambient_scope, ambient_context,
                                           scope_extra, context_extra)]
    if tag == 'i':
        return ['i', rename(p[1]), rename(p[2]),
                weaken(p[3], ambient_scope, ambient_context, scope_extra, context_extra)]
    if tag == 'e':
        return ['e', rename(p[1])] + [weaken(x, ambient_scope, ambient_context,
                                             scope_extra, context_extra) for x in p[2:]]
    if tag == 't':
        return ['t', rename(p[1]),
                weaken(p[2], ambient_scope, ambient_context, scope_extra, context_extra),
                weaken(p[3], ambient_scope, ambient_context, scope_extra, context_extra)]
    raise ValueError('unknown proof')


def ordinary_eliminate(goal, major, branch, context, scope):
    return ['e', goal, major, refl(-scope - 1), branch]


def numerical_cases(template, parameter, target, zero_proof, successor_builder,
                    context, scope):
    """Case rule, with no equality used: builder sees its own extended context."""
    matrix = bind(template, [W, parameter])
    goal = [matrix]
    fresh = -scope - 1
    body = opening(matrix, ONE, 1)
    base = opening(body, 0)
    intro_context = context + [(H, base)]
    step = successor_builder(fresh, intro_context, scope + 1)
    major = ['i', goal, ONE, step]
    result = at(template, parameter, target)
    branch = use(len(context), target,
                 weaken(zero_proof, scope, len(context), 1, 1))
    proof = ordinary_eliminate(result, major, branch, context, scope)
    assert derive(proof, context, scope) == result
    return proof


def transport(major, minor, template, parameter, context, scope):
    """s=t, h(s)=r ==> h(t)=r by the two-row naming packet."""
    source, target = derive(major, context, scope)
    left, right = derive(minor, context, scope)
    ensure = lambda condition: condition or (_ for _ in ()).throw(ValueError('macro mismatch'))
    ensure(left == at(template, parameter, source))
    hx = at(template, parameter, X)
    matrix_raw = [C(Y, 0, C(parity(Y), X, hx)),
                  C(Y, 0, C(parity(Y), target, right))]
    packet = D(matrix_raw)
    fresh = -scope - 1
    opened = opening(packet[0], source, 1)
    eta = fresh if len(opened) == 2 and source == 0 else 0
    intro_context = context + [(H, opening(opened, eta))]
    selector_template = [C(V, source, left), C(V, target, right)]
    zero_proof = weaken(major, scope, len(context), 1, 1)
    def successor_builder(z, extended, level):
        return weaken(minor, scope, len(context), 2, 2)
    step = numerical_cases(selector_template, V, parity(S(fresh)), zero_proof,
                           successor_builder, intro_context, scope + 1)
    packet_proof = ['i', packet, source, step]
    result = [at(template, parameter, target), right]
    equality = use(len(context), TWO, refl(0))
    branch = use(len(context), ONE, refl(0))
    proof = ['e', result, packet_proof, equality, branch]
    ensure(derive(proof, context, scope) == result)
    return proof


def symmetry(proof, context, scope):
    source, target = derive(proof, context, scope)
    return transport(proof, refl(source), V, V, context, scope)


def congruence(proof, template, parameter, context, scope):
    source, target = derive(proof, context, scope)
    return transport(symmetry(proof, context, scope),
                     refl(at(template, parameter, target)), template, parameter,
                     context, scope)


def transitivity(first, second, context, scope):
    a, b = derive(first, context, scope)
    c, d = derive(second, context, scope)
    assert b == c
    return transport(symmetry(first, context, scope), second, V, V, context, scope)


def crossed_transport(major, minor, template, parameter, context, scope):
    return symmetry(transport(major, minor, template, parameter, context, scope),
                    context, scope)


def equation_transport(equality, proof, template, parameter, context, scope):
    """Replace the parameter in both sides of one equation."""
    source, target = derive(equality, context, scope)
    left_template, right_template = template
    assert derive(proof, context, scope) == at(template, parameter, source)
    left = transport(equality, proof, left_template, parameter, context, scope)
    flipped = symmetry(left, context, scope)
    right = transport(equality, flipped, right_template, parameter, context, scope)
    return symmetry(right, context, scope)


def formula_identity(formula, context, scope):
    """Prove nested D-formulas whose final equation is literally reflexive."""
    if len(formula) == 2:
        assert formula[0] == formula[1]
        return refl(formula[0])
    body = opening(formula[0], 0, 1)
    fresh = -scope - 1
    eta = fresh if len(body) == 2 else 0
    local = opening(body, eta)
    expected = opening(body, S(fresh))
    branch = formula_identity(expected, context + [(H, local)], scope + 1)
    return ['i', formula, 0, branch]


def alias_zero(context, scope):
    packet = D([C(Y, 0, X), 0])
    return packet, ['i', packet, 0, refl(0)]


def repaired_zero_case(goal, case_builder, context, scope):
    """Recover case intro at witness0; case_builder consumes a base proof."""
    packet, major = alias_zero(context, scope)
    b = -scope - 1
    alias_body = opening(packet[0], b, 1)
    opened_context = context + [(opening(alias_body, 0), alias_body)]
    bzero = use(len(context), ONE, refl(0))
    z = -scope - 2
    matrix_b = opening(goal[0], b, 1)
    base_b = opening(matrix_b, 0)
    intro_context = opened_context + [(H, base_b)]
    bzero_here = weaken(bzero, scope + 1, len(opened_context), 1, 1)
    matrix_zero = opening(goal[0], 0, 1)
    base_zero = opening(matrix_zero, 0)
    base_template = opening(goal[0], 0)
    # After opening y at zero, x occupies positive index1. Convert to markerV.
    base_template = opening(base_template, V)
    converted_base = equation_transport(bzero_here, hypothesis(len(opened_context)),
                                        base_template, V, intro_context, scope + 2)
    step_zero = case_builder(z, converted_base, intro_context, scope + 2)
    step_template = opening(opening(goal[0], S(z)), V)
    reverse = symmetry(bzero_here, intro_context, scope + 2)
    step_b = equation_transport(reverse, step_zero, step_template, V,
                               intro_context, scope + 2)
    inner = ['i', goal, b, step_b]
    proof = ['e', goal, major, bzero, inner]
    assert derive(proof, context, scope) == goal
    return proof


def implication_equations(antecedent, consequent, builder):
    """Closed A -> B, for equation A/B. Builder works under its A assumption."""
    matrix = [C(Y, antecedent[0], consequent[0]),
              C(Y, antecedent[1], consequent[1])]
    goal = D(matrix)
    context = [(H, antecedent)]
    branch = builder(hypothesis(0), context, 1)
    proof = ['i', goal, ONE, branch]
    assert derive(proof, [], 0) == goal
    return {'goal': goal, 'proof': proof}


def implication_quantified_equation(antecedent, equation_template, parameter, builder):
    """A conditional universal equation with a nontrivial fresh parameter."""
    e_y = at(equation_template, parameter, Y)
    matrix = [C(Y, antecedent[0], e_y[0]), C(Y, antecedent[1], e_y[1])]
    goal = D(matrix)
    context = [(H, antecedent)]
    branch = builder(hypothesis(0), S(-1), context, 1)
    proof = ['i', goal, ONE, branch]
    assert derive(proof, [], 0) == goal
    return {'goal': goal, 'proof': proof}
