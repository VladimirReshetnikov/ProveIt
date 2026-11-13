"""Untrusted producers for the bounded-head proof checker.

The helper uses fresh named binders for readability, then lowers every hint
and proof branch to the checker's de Bruijn syntax. The checker imports none
of this file. The finite head search only constructs the displayed examples;
it is not part of the theory or the trusted checking boundary.
"""
import copy
import importlib.util
import itertools
import json
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('bounded_checker', ROOT / 'code/bounded_checker.py')
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


ONE = S(Z)
TWO = S(ONE)


def I(counter, seed, variable, body):
    return ('i', counter, seed, variable, body)


def C(counter, zero_value, successor_value):
    return I(counter, zero_value, fresh('u'), successor_value)


def P(counter):
    u = fresh('u')
    return I(counter, Z, u, C(V(u), ONE, Z))


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
    if tag == 'i':
        _, n, seed, binder, body = a
        return I(substitute(n, variable, value), substitute(seed, variable, value), binder,
                 body if binder == variable else substitute(body, variable, value))
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
    if tag == 'i':
        return free(a[1]) | free(a[2]) | (free(a[4]) - {a[3]})
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
    if tag == 'i':
        return ['i', encode(a[1], environment), encode(a[2], environment),
                encode(a[4], [a[3]] + environment)]
    if tag == 'q':
        return ['q', encode(a[2], [a[1]] + environment)]
    if tag == 'd':
        return ['d', encode(a[3], [a[2], a[1]] + environment)]
    return [tag] + [encode(b, environment) for b in a[1:]]


def same(a, b):
    environment = sorted(free(a) | free(b))
    return encode(a, environment) == encode(b, environment)


def encode_proof(p, environment):
    if p is None:
        return None
    rule, *a = p
    if rule == 'hc':
        depth, previous, branch = a
        return ['hc', depth, encode(previous, environment), encode_proof(branch, environment)]
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
        return ['di', encode(witness, environment),
                encode_proof(branch, [eigenvariable] + environment)]
    raise ValueError(rule)


def contract(a, depth):
    if a[0] != 'i':
        return None
    _, counter, seed, variable, body = a
    if depth:
        result = contract(counter, depth - 1)
        return None if result is None else I(result, seed, variable, body)
    if counter == Z:
        return seed
    if counter[0] == 's':
        return substitute(body, variable, I(counter[1], seed, variable, body))
    return None


def reduction_path(source, target):
    path = []
    for _ in range(256):
        if same(source, target):
            return path
        for depth in range(4):
            result = contract(source, depth)
            if result is not None:
                path.append((source, result, depth))
                source = result
                break
        else:
            return None
    return None


def left_conversion(proof, source, target):
    path = reduction_path(source, target)
    if path is None:
        path = reduction_path(target, source)
        if path is None:
            raise ValueError(('No displayed bounded path', source, target))
        path = [(b, a, depth) for a, b, depth in reversed(path)]
    for old, new, depth in path:
        proof = ('hc', depth, old, proof)
    return proof


def symmetry(equation, proof):
    left, right = equation[1:]
    x, y, z, b = (fresh(prefix) for prefix in ('x', 'y', 'z', 'b'))
    paired = D(x, y, E(C(V(y), Z, V(x)), Z))
    introduction = ('di', Z, z,
                    left_conversion(None, Z, C(S(V(z)), Z, Z)))
    closure = Q(y, E(C(V(y), Z, V(b)), Z))
    base = left_conversion(None, Z, C(Z, Z, V(b)))
    at_one = ('qe', closure, ONE, None, base)
    alias = left_conversion(at_one, C(ONE, Z, V(b)), V(b))
    reversed_equation = ('vs', b, Z, left, alias, proof)
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
        return E(C(index, Z, C(P(index), witness, h(witness))),
                 C(index, Z, C(P(index), t, result)))

    v = fresh('v')
    interpolation = Q(v, E(C(V(v), s, h(s)), C(V(v), t, result)))

    def successor_branch(fresh_index):
        goal = E(C(S(V(fresh_index)), s, h(s)), C(S(V(fresh_index)), t, result))
        return equation_conversion(minor_proof, E(h(s), result), goal)

    interpolation_proof = case_closure(interpolation, successor_branch)
    interpolation_base = equation_conversion(equality_proof, E(s, t),
                                              E(C(Z, s, h(s)), C(Z, t, result)))
    at_parity = ('qe', interpolation, P(S(V(z))), interpolation_proof,
                 interpolation_base)
    interpolation_goal = E(C(P(S(V(z))), s, h(s)), C(P(S(V(z))), t, result))
    paired = D(x, y, matrix(V(x), V(y)))
    introduction = ('di', s, z, equation_conversion(at_parity, interpolation_goal,
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
    data = {'variables': len(environment),
            'context': [encode(a, environment) for a in context],
            'goal': encode(goal, environment),
            'proof': encode_proof(proof, environment)}
    CHECKER.check(data)
    return data


def proof_rules(a, counts):
    if type(a) is list:
        if a and a[0] == 'hc':
            counts['hc_depth_' + str(a[1])] += 1
        for b in a:
            proof_rules(b, counts)
    elif type(a) is dict:
        for b in a.values():
            proof_rules(b, counts)


def main():
    tests = ROOT / 'tests'
    tests.mkdir(exist_ok=True)
    cases = []

    def save(name, data, expected, purpose):
        path = tests / (name + '.json')
        path.write_text(json.dumps(data, separators=(',', ':')) + '\n')
        cases.append({'file': path.name, 'expected': expected, 'purpose': purpose})

    s, t, r, c = map(V, ['s', 't', 'r', 'c'])
    save('symmetry_symbolic', certificate(['s', 't'], [E(s, t)], E(t, s),
                                         symmetry(E(s, t), None)), True,
         'Derived symmetry without a primitive right-endpoint conversion.')
    old = E(s, C(Z, t, ONE))
    save('right_conversion_derived', certificate(['s', 't'], [old], E(s, t),
                                               equation_conversion(None, old, E(s, t))), True,
         'Right-endpoint computation derived from symmetry and left HC.')

    def h(value):
        u, v = fresh('u'), fresh('v')
        return I(c, S(value), u, I(value, V(u), v, S(V(v))))

    goal = E(r, h(t))
    transport_proof = transport(s, t, r, h)
    transport_data = certificate(['s', 't', 'r', 'c'], [E(s, t), E(h(s), r)],
                                 goal, transport_proof)
    save('transport_symbolic', transport_data, True,
         'Full crossed transport through an iterator template; all packet rows are raw.')
    transport_counts = Counter()
    proof_rules(transport_data['proof'], transport_counts)
    assert transport_counts['hc_depth_3'] > 0

    # Exercise the literal-zero progress branch of the single introduction.
    save('transport_zero_source', certificate(['t', 'r', 'c'], [E(Z, t), E(h(Z), r)],
                                              E(r, h(t)), transport(Z, t, r, h)), True,
         'Transport packet introduced in the witness-zero progress mode.')
    def reducible_h(value):
        return C(Z, S(value), Z)
    save('transport_reducible_template', certificate(['s', 't', 'r'],
         [E(s, t), E(reducible_h(s), r)], E(r, reducible_h(t)),
         transport(s, t, r, reducible_h)), True,
         'The endpoint template is itself a raw head redex and must not be normalized.')

    x, y, z = fresh('x'), fresh('y'), fresh('z')
    alias_goal = D(x, y, E(C(V(y), s, s), r))
    zero_alias = C(Z, Z, Z)
    alias_branch = left_conversion(left_conversion(None, C(Z, s, s), s),
                                   s, C(S(V(z)), s, s))
    alias_case = certificate(['s', 'r'], [], alias_goal,
                             ('di', zero_alias, z, alias_branch))
    save('raw_zero_alias_case', alias_case, True,
         'A nonliteral zero alias selects the case premise, not the progressive premise.')
    changed = copy.deepcopy(alias_case)
    changed['proof'][1] = ['z']
    save('reject_wrong_intro_mode', changed, False,
         'The same branch no longer checks when the literal-zero witness selects progress.')
    save('zero_computation', certificate(['s'], [], E(C(Z, s, ONE), s),
                                         left_conversion(None, s, C(Z, s, ONE))), True,
         'Zero computation is a derived HC expansion from reflexivity.')
    u = fresh('u')
    term = I(S(c), s, u, S(V(u)))
    reduct = contract(term, 0)
    save('successor_computation', certificate(['s', 'c'], [], E(term, reduct),
                                              left_conversion(None, reduct, term)), True,
         'Raw successor computation from one left HC expansion.')

    # A depth-three contraction is an accepted rule instance; depth four is not.
    def tower(depth):
        term = C(Z, ONE, Z)
        for _ in range(depth):
            term = C(term, ONE, Z)
        return term

    for depth, expected in [(3, True), (4, False)]:
        term = tower(depth)
        reduced = contract(term, depth)
        data = {'variables': 0, 'context': [encode(E(term, Z), [])],
                'goal': encode(E(reduced, Z), []),
                'proof': ['hc', depth, encode(term, []), None]}
        save('counter_depth_' + str(depth), data, expected,
             'The supplied counter-spine address is checked against the literal bound three.')
    term = tower(1)
    save('reject_boolean_depth', {'variables': 0, 'context': [encode(E(term, Z), [])],
         'goal': encode(E(contract(term, 1), Z), []),
         'proof': ['hc', True, encode(term, []), None]}, False,
         'A Boolean must not masquerade as the counter-spine depth one.')

    # An iterator in a seed is outside the permitted address grammar.
    seed_redex = C(Z, ONE, Z)
    before = C(c, seed_redex, Z)
    after = C(c, ONE, Z)
    save('reject_seed_conversion', {'variables': 1, 'context': [encode(E(before, Z), ['c'])],
                                    'goal': encode(E(after, Z), ['c']),
                                    'proof': ['hc', 1, encode(before, ['c']), None]}, False,
         'HC cannot travel into an iterator seed.')
    save('reject_direct_right_conversion', {'variables': 0,
         'context': [encode(E(Z, seed_redex), [])], 'goal': encode(E(Z, ONE), []),
         'proof': ['hc', 0, encode(seed_redex, []), None]}, False,
         'A direct right-endpoint HC instruction is unavailable.')

    malformed = {'variables': 0, 'context': [], 'goal': ['=', ['s', ['z']], ['z']],
                 'proof': ['hc', 0, ['i', ['z'], ['z'], ['v', 999]], None]}
    save('reject_erased_scope', malformed, False,
         'An out-of-scope raw body is rejected before zero erasure.')
    malformed = copy.deepcopy(malformed)
    malformed['proof'][2][3] = ['=', ['z'], ['z']]
    save('reject_erased_sort', malformed, False,
         'A formula in an iterator body is rejected before zero erasure.')
    save('scoped_erased_body', {'variables': 1, 'context': [],
         'goal': ['=', ['i', ['z'], ['z'], ['v', 1]], ['z']],
         'proof': ['hc', 0, ['z'], None]}, True,
         'An ambient parameter is allowed in a dead body when it is in scope.')
    save('reject_unused_qe_hint_scope', {'variables': 0,
         'context': [['q', ['=', ['z'], ['z']]]], 'goal': ['=', ['z'], ['z']],
         'proof': ['qe', ['=', ['z'], ['z']], ['i', ['z'], ['z'], ['v', 99]], None, None]},
         False, 'An unused specialization hint is validated even for a reflexive target.')
    malformed = copy.deepcopy(transport_data)
    malformed['variables'] = True
    save('reject_boolean_scope', malformed, False, 'Boolean values are not numerical scope sizes.')
    malformed = {'variables': 0, 'context': [], 'goal': ['=', ['z'], ['s', ['z']]], 'proof': None}
    save('reject_contradiction', malformed, False, 'A false closed equation is not reflexivity.')
    malformed = {'variables': 1, 'context': [['=', ['v', 0], ['z']]],
                 'goal': ['=', ['z'], ['v', 0]],
                 'proof': ['vs', True, ['z'], ['v', 0], None, None]}
    save('reject_boolean_variable', malformed, False, 'Boolean values are not substitution indices.')
    malformed = {'variables': 0, 'context': [], 'goal': ['=', ['v', 0], ['v', 0]], 'proof': None}
    save('reject_public_free_variable', malformed, False, 'Even a reflexive goal must be in scope.')

    # Substitution may contain its source variable; it makes exactly one pass.
    save('self_containing_replacement', {'variables': 1,
         'context': [['=', ['v', 0], ['s', ['v', 0]]], ['=', ['v', 0], ['z']]],
         'goal': ['=', ['z'], ['s', ['v', 0]]],
         'proof': ['vs', 0, ['s', ['v', 0]], ['v', 0], None, None]}, True,
         'Variable replacement has no occurs check and does not iterate itself.')
    for case in cases:
        data = json.loads((tests / case['file']).read_text())
        try:
            CHECKER.check(data)
            accepted = True
        except Exception:
            accepted = False
        if accepted != case['expected']:
            raise ValueError(('Unexpected generated result', case, accepted))
    (tests / 'cases.json').write_text(json.dumps(cases, indent=2) + '\n')
    receipt = {'cases': len(cases), 'transport_hc_counts': dict(sorted(transport_counts.items())),
               'transport_certificate_bytes': (tests / 'transport_symbolic.json').stat().st_size,
               'trusted_generator': False}
    (ROOT / 'evidence' / 'generation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
