"""Untrusted named-syntax producer; no component is imported by the checker.

The proof architecture follows ConciseIPRA/Artifacts/bounded_head's producer.
Its parity packet is replaced by a counter-aware three-row recursor. All
computational paths here contract at the root, and no normalizer is trusted.
"""
import copy
import importlib.util
import itertools
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('root_checker', ROOT / 'code/root_checker.py')
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)
NAMES = itertools.count()


def fresh(prefix='b'):
    return prefix + str(next(NAMES))


def V(name):
    return ('v', name)


Z = ('z',)


def S(a):
    return ('s', a)


ONE, TWO = S(Z), S(S(Z))


def R(counter, seed, index, state, body):
    return ('r', counter, seed, index, state, body)


def C(counter, zero_value, successor_value):
    return R(counter, zero_value, fresh('i'), fresh('u'), successor_value)


def T(counter, zero_value, one_value, later_value):
    i, u = fresh('i'), fresh('u')
    return R(counter, zero_value, i, u, C(V(i), one_value, later_value))


def E(left, right):
    return ('=', left, right)


def Q(variable, body):
    return ('q', variable, body)


def D(witness, variable, body):
    return ('d', witness, variable, body)


def substitute(a, variable, value):
    tag = a[0]
    if tag == 'v':
        return value if a[1] == variable else a
    if tag == 'z':
        return a
    if tag == 'r':
        _, n, seed, index, state, body = a
        return R(substitute(n, variable, value), substitute(seed, variable, value), index, state,
                 body if variable in (index, state) else substitute(body, variable, value))
    if tag == 'q':
        return a if a[1] == variable else Q(a[1], substitute(a[2], variable, value))
    if tag == 'd':
        return a if variable in a[1:3] else D(a[1], a[2], substitute(a[3], variable, value))
    return (tag,) + tuple(substitute(b, variable, value) for b in a[1:])


def free(a):
    tag = a[0]
    if tag == 'v':
        return {a[1]}
    if tag == 'z':
        return set()
    if tag == 'r':
        return free(a[1]) | free(a[2]) | (free(a[5]) - set(a[3:5]))
    if tag == 'q':
        return free(a[2]) - {a[1]}
    if tag == 'd':
        return free(a[3]) - set(a[1:3])
    return set().union(*(free(b) for b in a[1:]))


def encode(a, environment):
    tag = a[0]
    if tag == 'v':
        return ['v', environment.index(a[1])]
    if tag == 'z':
        return ['z']
    if tag == 'r':
        return ['r', encode(a[1], environment), encode(a[2], environment),
                encode(a[5], [a[4], a[3]] + environment)]
    if tag == 'q':
        return ['q', encode(a[2], [a[1]] + environment)]
    if tag == 'd':
        return ['d', encode(a[3], [a[2], a[1]] + environment)]
    return [tag] + [encode(b, environment) for b in a[1:]]


def same(a, b):
    return encode(a, sorted(free(a) | free(b))) == encode(b, sorted(free(a) | free(b)))


def encode_proof(p, environment):
    if p is None:
        return None
    rule, *a = p
    if rule == 'rc':
        previous, branch = a
        return ['rc', encode(previous, environment), encode_proof(branch, environment)]
    if rule == 'vs':
        variable, value, left_term, major, minor = a
        return ['vs', environment.index(variable), encode(value, environment),
                encode(left_term, environment), encode_proof(major, environment),
                encode_proof(minor, environment)]
    if rule == 'qe':
        closure, value, major, base = a
        return ['qe', encode(closure, environment)[1], encode(value, environment),
                encode_proof(major, environment), encode_proof(base, environment)]
    if rule == 'de':
        paired, major, eigenvariable, branch = a
        return ['de', encode(paired, environment)[1], encode_proof(major, environment),
                encode_proof(branch, [eigenvariable] + environment)]
    if rule == 'di':
        witness, eigenvariable, branch = a
        return ['di', encode(witness, environment), encode_proof(branch, [eigenvariable] + environment)]
    raise ValueError(rule)


def contract(a):
    if a[0] != 'r':
        return None
    _, counter, seed, index, state, body = a
    if counter == Z:
        return seed
    if counter[0] == 's':
        return substitute(substitute(body, index, counter[1]), state,
                          R(counter[1], seed, index, state, body))
    return None


def reduction_path(source, target):
    path = []
    for _ in range(128):
        if same(source, target):
            return path
        result = contract(source)
        if result is None:
            return None
        path.append((source, result))
        source = result
    return None


def left_conversion(proof, source, target):
    path = reduction_path(source, target)
    if path is None:
        path = reduction_path(target, source)
        if path is None:
            raise ValueError(('No displayed root path', source, target))
        path = [(b, a) for a, b in reversed(path)]
    for old, new in path:
        proof = ('rc', old, proof)
    return proof


def symmetry(equation, proof):
    left, right = equation[1:]
    x, y, z, b = (fresh(prefix) for prefix in ('x', 'y', 'z', 'b'))
    paired = D(x, y, E(Z, Z))
    introduction = ('di', Z, z, None)
    reversed_equation = ('vs', b, V(b), left, None, proof)
    return ('de', paired, introduction, b, reversed_equation)


def equation_conversion(proof, source, target):
    proof = left_conversion(proof, source[1], target[1])
    if not same(source[2], target[2]):
        proof = symmetry(E(target[1], source[2]), proof)
        proof = left_conversion(proof, source[2], target[2])
        proof = symmetry(E(target[2], target[1]), proof)
    return proof


def case_closure(closure, branch_builder):
    y, body = closure[1:]
    x, z, b = (fresh(prefix) for prefix in ('x', 'z', 'b'))
    paired = D(x, y, body)
    introduction = ('di', ONE, z, branch_builder(z))
    return ('de', paired, introduction, b, None)


def transport(s, t, result, h, equality_proof=None, minor_proof=None):
    x, y, z, b = (fresh(prefix) for prefix in ('x', 'y', 'z', 'b'))

    def matrix(witness, index):
        return E(T(index, Z, h(witness), witness), T(index, Z, result, t))

    v = fresh('v')
    interpolation = Q(v, E(C(V(v), h(s), s), C(V(v), result, t)))

    def successor_branch(fresh_index):
        goal = E(C(S(V(fresh_index)), h(s), s), C(S(V(fresh_index)), result, t))
        return equation_conversion(equality_proof, E(s, t), goal)

    interpolation_proof = case_closure(interpolation, successor_branch)
    interpolation_base = equation_conversion(minor_proof, E(h(s), result),
                                              E(C(Z, h(s), s), C(Z, result, t)))
    at_index = ('qe', interpolation, V(z), interpolation_proof, interpolation_base)
    interpolation_goal = E(C(V(z), h(s), s), C(V(z), result, t))
    paired = D(x, y, matrix(V(x), V(y)))
    introduction = ('di', s, z, equation_conversion(at_index, interpolation_goal,
                                                   matrix(s, S(V(z)))))
    closure = Q(y, matrix(V(b), V(y)))

    def row(index, target):
        base = equation_conversion(None, E(Z, Z), matrix(V(b), Z))
        instance = ('qe', closure, index, None, base)
        return equation_conversion(instance, matrix(V(b), index), target)

    minor = row(ONE, E(h(V(b)), result))
    major = row(TWO, E(V(b), t))
    final = ('vs', b, t, h(V(b)), major, minor)
    return ('de', paired, introduction, b, final)


def certificate(environment, context, goal, proof):
    data = {'variables': len(environment), 'context': [encode(a, environment) for a in context],
            'goal': encode(goal, environment), 'proof': encode_proof(proof, environment)}
    CHECKER.check(data)
    return data


def count_rules(value, counts):
    if type(value) is list:
        if value and value[0] in ('rc', 'vs', 'qe', 'de', 'di'):
            counts[value[0]] += 1
        for child in value:
            count_rules(child, counts)


def main():
    cases = []

    def save(name, data, expected, purpose):
        path = ROOT / 'tests' / (name + '.json')
        path.write_text(json.dumps(data, separators=(',', ':')) + '\n')
        cases.append({'file': path.name, 'expected': expected, 'purpose': purpose})

    s, t, r, c = map(V, ['s', 't', 'r', 'c'])
    save('symmetry_symbolic', certificate(['s', 't'], [E(s, t)], E(t, s),
         symmetry(E(s, t), None)), True, 'Symmetry derived using reflexivity of a fresh unused parameter.')
    old = E(s, C(Z, t, ONE))
    save('right_conversion_derived', certificate(['s', 't'], [old], E(s, t),
         equation_conversion(None, old, E(s, t))), True, 'Right conversion through derived symmetry.')

    def h(value):
        i, u, j, v = (fresh(prefix) for prefix in ('i', 'u', 'j', 'v'))
        return R(c, S(value), i, u, R(value, V(u), j, v, R(V(i), V(v), fresh('k'), fresh('w'), S(value))))

    data = certificate(['s', 't', 'r', 'c'], [E(s, t), E(h(s), r)],
                       E(r, h(t)), transport(s, t, r, h))
    save('transport_symbolic', data, True, 'General transport inside nested raw recursors and both bound coordinates.')
    counts = Counter()
    count_rules(data['proof'], counts)
    save('transport_zero_source', certificate(['t', 'r', 'c'], [E(Z, t), E(h(Z), r)],
         E(r, h(t)), transport(Z, t, r, h)), True, 'The literal-zero progress mode needs no use of its assumption.')
    old_term = C(c, S(s), r)
    save('transport_older_parameter_term', certificate(['s', 'r', 'c'],
         [E(s, old_term), E(h(s), r)], E(r, h(old_term)), transport(s, old_term, r, h)),
         True, 'The replacement is a compound term with several older parameters, under nested binders.')
    save('transport_reducible_template', certificate(['s', 't', 'r'],
         [E(s, t), E(C(Z, S(s), Z), r)], E(r, C(Z, S(t), Z)),
         transport(s, t, r, lambda a: C(Z, S(a), Z))), True, 'A reducible endpoint remains raw in transport.')
    save('zero_computation', certificate(['s'], [], E(C(Z, s, ONE), s),
         left_conversion(None, s, C(Z, s, ONE))), True, 'Zero equation is a root expansion of reflexivity.')

    i, u, j, v = (fresh(prefix) for prefix in ('i', 'u', 'j', 'v'))
    term = R(S(c), s, i, u, R(V(i), V(u), j, v, S(V(i))))
    reduct = contract(term)
    save('successor_computation', certificate(['s', 'c'], [], E(term, reduct),
         left_conversion(None, reduct, term)), True, 'Both predecessor counter and previous state are opened under a nested recursor.')
    index_term = R(S(c), s, i, u, V(i))
    state_term = R(S(c), s, i, u, V(u))
    save('counter_projection', certificate(['s', 'c'], [], E(index_term, c),
         left_conversion(None, c, index_term)), True, 'Counter is the prior counter, not the state.')
    save('state_projection', certificate(['s', 'c'], [], E(state_term, contract(state_term)),
         left_conversion(None, contract(state_term), state_term)), True, 'State is the prior recursive call.')
    wrong = {'variables': 2, 'context': [],
             'goal': encode(E(index_term, R(c, s, i, u, V(i))), ['s', 'c']),
             'proof': ['rc', encode(R(c, s, i, u, V(i)), ['s', 'c']), None]}
    save('reject_swapped_binders', wrong, False, 'Swapping the two body binders is rejected.')

    x, y, z = fresh('x'), fresh('y'), fresh('z')
    alias_goal = D(x, y, E(C(V(y), s, s), r))
    alias_branch = left_conversion(left_conversion(None, C(Z, s, s), s), s, C(S(V(z)), s, s))
    alias = certificate(['s', 'r'], [], alias_goal, ('di', C(Z, Z, Z), z, alias_branch))
    save('raw_zero_alias_case', alias, True, 'A nonliteral zero alias preserves the case mode.')
    bad = copy.deepcopy(alias)
    bad['proof'][1] = ['z']
    save('reject_wrong_intro_mode', bad, False, 'Literal zero switches the equation introduction to progress.')

    seed_redex = C(Z, ONE, Z)
    for name, before, after in (
        ('counter', C(seed_redex, ONE, Z), C(ONE, ONE, Z)),
        ('zero_counter', C(C(Z, Z, Z), ONE, Z), C(Z, ONE, Z)),
        ('seed', C(c, seed_redex, Z), C(c, ONE, Z)),
        ('successor_child', S(seed_redex), S(ONE)),
    ):
        env = sorted(free(before) | free(after))
        save('reject_' + name + '_descent', {'variables': len(env),
             'context': [encode(E(before, Z), env)], 'goal': encode(E(after, Z), env),
             'proof': ['rc', encode(before, env), None]}, False, 'Root conversion does not descend into ' + name + '.')
    save('reject_direct_right_conversion', {'variables': 0,
         'context': [encode(E(Z, seed_redex), [])], 'goal': encode(E(Z, ONE), []),
         'proof': ['rc', encode(seed_redex, []), None]}, False, 'The primitive conversion changes only the left endpoint.')
    bad = {'variables': 0, 'context': [], 'goal': ['=', ['z'], ['z']],
           'proof': ['rc', ['r', ['z'], ['z'], ['v', 2]], None]}
    save('reject_erased_scope', bad, False, 'An invalid body is checked before zero contraction erases it.')
    bad = copy.deepcopy(bad)
    bad['proof'][1][3] = ['=', ['z'], ['z']]
    save('reject_erased_sort', bad, False, 'A formula cannot be hidden in an erased recursor body.')
    save('scoped_erased_body', {'variables': 1, 'context': [],
         'goal': ['=', ['r', ['z'], ['z'], ['v', 2]], ['z']],
         'proof': ['rc', ['z'], None]}, True, 'The two binders and one ambient parameter are in scope.')
    save('reject_unused_qe_hint_scope', {'variables': 0,
         'context': [['q', ['=', ['z'], ['z']]]], 'goal': ['=', ['z'], ['z']],
         'proof': ['qe', ['=', ['z'], ['z']], ['r', ['z'], ['z'], ['v', 99]], None, None]},
         False, 'A specialization hint is validated even when its variable is unused.')
    for name, value in [('boolean', True), ('float', 0.0), ('negative', -1)]:
        save('reject_' + name + '_scope', {'variables': value, 'context': [],
             'goal': ['=', ['z'], ['z']], 'proof': None}, False, 'Scope counts are exact nonnegative integers.')
    save('reject_boolean_variable', {'variables': 1, 'context': [],
         'goal': ['=', ['v', True], ['v', True]], 'proof': None}, False, 'Boolean variable coordinates are rejected.')
    save('reject_public_free_variable', {'variables': 0, 'context': [],
         'goal': ['=', ['v', 0], ['v', 0]], 'proof': None}, False, 'A reflexive goal still requires valid scope.')
    save('reject_contradiction', {'variables': 0, 'context': [],
         'goal': ['=', ['z'], ['s', ['z']]], 'proof': None}, False, 'The closed contradiction is not a leaf theorem.')
    save('self_containing_replacement', {'variables': 1,
         'context': [['=', ['v', 0], ['s', ['v', 0]]], ['=', ['v', 0], ['z']]],
         'goal': ['=', ['z'], ['s', ['v', 0]]],
         'proof': ['vs', 0, ['s', ['v', 0]], ['v', 0], None, None]}, True,
         'Free-variable replacement is one pass and permits a self-containing replacement.')
    for case in cases:
        try:
            CHECKER.check(json.loads((ROOT / 'tests' / case['file']).read_text()))
            accepted = True
        except Exception:
            accepted = False
        if accepted != case['expected']:
            raise ValueError(('Unexpected result', case, accepted))
    (ROOT / 'tests/cases.json').write_text(json.dumps(cases, indent=2) + '\n')
    receipt = {'cases': len(cases), 'transport_rule_counts': dict(counts),
               'transport_certificate_bytes': (ROOT / 'tests/transport_symbolic.json').stat().st_size,
               'trusted_generator': False, 'contraction_locations': 'root only'}
    (ROOT / 'evidence/generation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
