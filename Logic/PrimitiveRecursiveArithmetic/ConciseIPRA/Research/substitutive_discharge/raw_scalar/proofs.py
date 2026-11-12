"""Untrusted proof constructors for the contextual-discharge checker."""
from checker import opening


H0 = [[0, 0, 0], 0]
ONE = [0, 0]


def numeral(n):
    return 0 if n == 0 else [0, numeral(n - 1)]


def calc(term):
    return ['c', term]


def truth():
    return calc(H0[0])


def trivial():
    return ['i', [H0], ONE, truth()]


def hypothesis(index, target=0):
    return ['u', index, target, truth()]


def rename_syntax(a, scope):
    if type(a) is int:
        return a - (a < -scope)
    return [rename_syntax(t, scope) for t in a]


def weaken(proof, scope, count):
    """Append one clause/parameter before the proof's own local scopes."""
    tag, *a = proof
    if tag == 'c':
        return [tag, rename_syntax(a[0], scope)]
    if tag == 'u':
        j, t, p = a
        return [tag, j + (j >= count), rename_syntax(t, scope), weaken(p, scope, count)]
    if tag == 'i':
        goal, t, p = a
        return [tag, rename_syntax(goal, scope), rename_syntax(t, scope), weaken(p, scope, count)]
    if tag == 'e':
        goal, template, major, equality, branch = a
        return [tag, rename_syntax(goal, scope), rename_syntax(template, scope),
                weaken(major, scope, count), weaken(equality, scope, count),
                weaken(branch, scope, count)]
    raise ValueError('unknown constructor')


def transport(template, target, equality, minor, scope=0, count=0):
    return ['e', opening(template, target), template, trivial(),
            weaken(equality, scope, count), weaken(minor, scope, count)]


def reflexivity(t, scope=0, count=0):
    w = [0, t, 0]
    return transport([1, t], t, calc(w), calc(w), scope, count)


def symmetry(s, t, equality, scope=0, count=0):
    return transport([1, s], t, equality, reflexivity(s, scope, count), scope, count)


def transitivity(s, t, u, first, second, scope=0, count=0):
    return transport([s, 1], u, second, first, scope, count)


def ordinary_elimination(goal, major, branch):
    return ['e', goal, goal, major, truth(), branch]


def iterator_identity():
    # D's outer witness is unused. The inner coordinate is y (index 1).
    matrix = [[1, 0, [0, 1]], 1]
    z = -1
    predecessor = [z, 0, [0, 1]]
    successor = [[0, z], 0, [0, 1]]
    template = [successor, [0, 1]]
    branch = transport(template, z, hypothesis(0), calc(successor), 1, 1)
    return [matrix], ['i', [matrix], 0, branch]


def instantiate_identity(n):
    major_goal, major = iterator_identity()
    t = numeral(n)
    goal = [[t, 0, [0, 1]], t]
    base = calc([0, 0, [0, 1]])
    branch = ['u', 0, t, base]
    return goal, ordinary_elimination(goal, major, branch)


def fixtures():
    cases = {}
    def add(name, goal, proof):
        cases[name] = {'goal': goal, 'proof': proof}
    a = numeral(2)
    z = [0, a, [0, 1]]
    add('zero_computation', [z, a], calc(z))
    b = [ONE, a, [0, 1]]
    add('successor_computation', [b, [0, z]], calc(b))
    for name, t in [('zero', 0), ('successor', ONE), ('redex', z),
                    ('nested_binder', [a, 0, [1, 1, [0, 2]]])]:
        add('reflexivity_' + name, [t, t], reflexivity(t))
    add('symmetry_of_zero_computation', [a, z], symmetry(z, a, calc(z)))
    source = [0, a, 0]
    template = [[a, 1, [0, 2]], [a, source, [0, source]]]
    minor_term = template[1]
    add('capture_avoiding_iterator_template', opening(template, a),
        transport(template, a, calc(source), reflexivity(minor_term)))
    matrix = [source, a]
    minor = ['i', [matrix], ONE, hypothesis(0)]
    compound_template = [[3, a]]
    add('template_beneath_D', opening(compound_template, a),
        transport(compound_template, a, calc(source), minor))
    g, p = iterator_identity()
    add('equation_induction_uses_hypothesis', g, p)
    for n in (0, 1, 3):
        g, p = instantiate_identity(n)
        add('ordinary_elimination_' + str(n), g, p)
    # A compound conclusion, with a witness depending on an already-opened
    # parameter, is retained under ordinary elimination before discharge.
    compound = [[[1, 0, [0, 1]], 1]]
    add('compound_ordinary_elimination', compound,
        ordinary_elimination(compound, trivial(), weaken(iterator_identity()[1], 0, 0)))
    return cases
