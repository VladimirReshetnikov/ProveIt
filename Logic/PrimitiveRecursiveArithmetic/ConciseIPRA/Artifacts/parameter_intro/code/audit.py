"""Independent named-variable normalizer and finite inference audit.

This is untrusted verification support, never imported by the checkers.
"""
from pathlib import Path
import ast
import copy
import itertools
import json
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def module(name):
    path = ROOT / name
    tree = ast.parse(path.read_text())
    tree.body = [n for n in tree.body if isinstance(n, (ast.Import, ast.FunctionDef))]
    result = {}
    exec(compile(tree, str(path), 'exec'), result)
    return result


primary = module('checker.py')
validated = module('control_template_validation.py')
repaired = primary
simultaneous = module('audit_multisub.py')
names = itertools.count()


def decode(a, bound=(), form=False):
    if type(a) is int:
        assert not form
        if a == 0:
            return ('zero',)
        if a < 0:
            return ('free', a)
        return ('var', bound[a - 1])
    assert type(a) is list
    if form:
        if len(a) == 2:
            return ('eq', decode(a[0], bound), decode(a[1], bound))
        assert len(a) == 1
        x, y = next(names), next(names)
        return ('d', x, y, decode(a[0], (y, x) + bound, True))
    assert len(a) == 3
    counter, state = next(names), next(names)
    return ('r', decode(a[0], bound), decode(a[1], bound), counter, state,
            decode(a[2], (state, counter) + bound))


def replace(a, mapping):
    tag = a[0]
    if tag == 'var':
        return mapping.get(a[1], a)
    if tag in ('zero', 'free'):
        return a
    if tag == 's':
        return ('s', replace(a[1], mapping))
    if tag == 'r':
        return ('r', replace(a[1], mapping), replace(a[2], mapping),
                a[3], a[4], replace(a[5], {k: v for k, v in mapping.items() if k not in (a[3], a[4])}))
    if tag == 'eq':
        return ('eq', replace(a[1], mapping), replace(a[2], mapping))
    return ('d', a[1], a[2], replace(a[3], {k: v for k, v in mapping.items() if k not in (a[1], a[2])}))


def normal(a):
    tag = a[0]
    if tag in ('zero', 'free', 'var'):
        return a
    if tag == 's':
        return ('s', normal(a[1]))
    if tag == 'eq':
        return ('eq', normal(a[1]), normal(a[2]))
    if tag == 'd':
        return ('d', a[1], a[2], normal(a[3]))
    c, seed, h = normal(a[1]), normal(a[2]), normal(a[5])
    if c[0] == 'zero':
        return ('s', seed)
    if c[0] == 's':
        previous = normal(('r', c[1], seed, a[3], a[4], h))
        return normal(replace(h, {a[3]: c[1], a[4]: previous}))
    return ('r', c, seed, a[3], a[4], h)


def encode(a, bound=()):
    tag = a[0]
    if tag == 'zero':
        return 0
    if tag == 'free':
        return a[1]
    if tag == 'var':
        return bound.index(a[1]) + 1
    if tag == 's':
        return [0, encode(a[1], bound), 0]
    if tag == 'eq':
        return [encode(a[1], bound), encode(a[2], bound)]
    if tag == 'd':
        return [encode(a[3], (a[2], a[1]) + bound)]
    return [encode(a[1], bound), encode(a[2], bound),
            encode(a[5], (a[4], a[3]) + bound)]


def random_term(rng, size, depth):
    leaves = [0, -1, -2] + list(range(1, depth + 1))
    if size == 0 or rng.randrange(3) == 0:
        return rng.choice(leaves)
    if rng.randrange(3) == 0:
        return [0, random_term(rng, size - 1, depth), 0]
    # Literal zero/one or a parameter keeps numeric experiments inexpensive.
    c = rng.choice(leaves + [[0, 0, 0]])
    return [c, random_term(rng, size - 1, depth),
            random_term(rng, size - 1, depth + 2)]


def numeric(a, free, bound=()):
    if type(a) is int:
        return 0 if a == 0 else free[a] if a < 0 else bound[a - 1]
    counter = numeric(a[0], free, bound)
    state = numeric(a[1], free, bound) + 1
    for index in range(counter):
        state = numeric(a[2], free, (state, index) + bound)
    return state


def normalization_audit():
    rng = random.Random(11814771)
    counts = dict(normal_forms=0, numerical_values=0, openings=0,
                  successor_contractions=0, capture_controls=0)
    for depth in range(4):
        outer = tuple(next(names) for _ in range(depth))
        for _ in range(100):
            a = random_term(rng, 3, depth)
            expected = encode(normal(decode(a, outer)), outer)
            actual = primary['walk'](a, lambda i, d: i)
            assert actual == expected, (a, actual, expected)
            assert simultaneous['walk'](a, lambda i, d: i) == expected
            counts['normal_forms'] += 1
            for _ in range(3):
                values = tuple(rng.randrange(3) for _ in outer)
                free = {-1: rng.randrange(3), -2: rng.randrange(3)}
                assert numeric(a, free, values) == numeric(actual, free, values)
                counts['numerical_values'] += 1
        for protected in range(2):
            prefix = tuple(next(names) for _ in range(protected))
            target = next(names)
            for _ in range(60):
                a = random_term(rng, 2, depth + protected + 1)
                t = random_term(rng, 2, depth)
                named = decode(a, prefix + (target,) + outer)
                image = decode(t, outer)
                expected = encode(normal(replace(named, {target: image})), prefix + outer)
                actual = primary['sub'](a, t, protected)
                assert actual == expected, (a, t, protected, actual, expected)
                counts['openings'] += 1
        for _ in range(80):
            c = random_term(rng, 1, depth)
            seed = random_term(rng, 1, depth)
            h = random_term(rng, 2, depth + 2)
            a = [[0, c, 0], seed, h]
            expected = encode(normal(decode(a, outer)), outer)
            assert primary['walk'](a, lambda i, d: i) == expected, (depth, a, primary['walk'](a, lambda i, d: i), expected, simultaneous['walk'](a, lambda i, d: i))
            assert simultaneous['walk'](a, lambda i, d: i) == expected
            counts['successor_contractions'] += 1
    # State-first opening without a lift would confuse the outer counter/state.
    raw = [-1, 0, [[0, 2, 0], 0, 1]]
    expected = [-1, 0, [2, 0, 1]]
    assert primary['walk'](raw, lambda i, d: i) == expected
    counts['capture_controls'] += 1
    # The predecessor equation is a literal normalization identity.
    assert primary['walk']([[0, -1, 0], 0, 2], lambda i, d: i) == -1
    counts['capture_controls'] += 1
    return counts


ONE = [0, 0, 0]
S = lambda t: [0, t, 0]
U = lambda j, t=0, p=None: ['u', j, t, p]
REF = lambda t: U(0, t)
TRUTH = [0, 0]
DUMMY = ['i', REF(0)]
ID = [[1, 0, 1], ONE]


def nf(a):
    return primary['walk'](a, lambda i, d: i)


def shift(a, amount):
    return primary['walk'](a, lambda i, d: i + amount if i > d else i)


def predecessor(t):
    return nf([t, 0, 2])


def select(y, a, b):
    return predecessor([y, a, S(shift(b, 2))])


def gate(formula, y):
    if len(formula) == 2:
        return [select(y, 0, formula[0]), select(y, 0, formula[1])]
    return [gate(formula[0], shift(y, 2))]


def naming(t):
    return [[select(1, 0, 2), select(1, 0, shift(t, 2))]]


def bind_two(a, x, y):
    return [primary['walk'](a, lambda i, d:
                           d + 1 if i == y else d + 2 if i == x
                           else i + 2 if i > d else i)]


def naming_proof(t, context_length=1):
    # Q_y gate(y, Name(P(y))) is represented as D with an unused first slot.
    y, x = -1000, -1001
    closure = bind_two(gate(naming(predecessor(y)), y), x, y)
    fresh = -context_length
    closure_proof = ['i', ['i', REF(fresh)]]
    # Ordinary elimination is generalized discharge with a constant template.
    return ['e', closure[0], naming(t), 0, 0, closure_proof,
            REF(0), U(context_length, S(t), DUMMY)]


def examples():
    result = {}
    def add(name, goal, proof):
        result[name] = [goal, proof]
    add('reflexivity_zero', [0, 0], REF(0))
    add('reflexivity_one', [ONE, ONE], REF(ONE))
    add('dummy_D', [TRUTH], DUMMY)
    add('case_false', [[0, ONE]], ['i', U(1)])
    add('compound_case', [[[0, ONE]]], ['i', U(1)])
    add('used_progress_hypothesis', [ID], ['i', U(1)])
    add('dummy_elimination', TRUTH,
        ['e', TRUTH, TRUTH, 0, 0, DUMMY, REF(0), REF(0)])
    rb = [-1, 0, 1]
    target = [[S([1, 0, 1]), S(ONE)]]
    branch = ['e', ID, [S(rb), S(1)], rb, ONE,
              ['i', U(2)], U(2, -1, REF(ONE)), REF(S(rb))]
    add('transport_through_successor', target, ['i', branch])
    target2 = [[[S([3, 0, 1]), S(ONE)]]]
    template2 = [[S(rb), S(3)]]
    branch2 = ['e', ID, template2, rb, ONE,
               ['i', U(2)], U(2, -1, REF(ONE)), ['i', REF(S(rb))]]
    add('transport_through_D', target2, ['i', branch2])
    add('name_one_without_witness', naming(ONE), naming_proof(ONE))
    add('name_two_without_witness', naming(S(ONE)), naming_proof(S(ONE)))
    add('erased_extra_bound_template', [ONE, ONE],
        ['e', TRUTH, [[1, 0, 99], ONE], 0, 0, DUMMY, REF(0), REF(ONE)])
    add('erased_extra_free_template', [ONE, ONE],
        ['e', TRUTH, [[1, 0, -99], ONE], 0, 0, DUMMY, REF(0), REF(ONE)])
    return result


def main():
    counts = normalization_audit()
    positives = examples()
    for name, (goal, proof) in positives.items():
        primary['prove'](goal, proof, [([], [1, 1])])
        repaired['prove'](goal, proof, [([], [1, 1])])
        path = ROOT / 'examples' / (name + '.json')
        path.parent.mkdir(exist_ok=True)
        path.write_text(json.dumps([goal, proof], separators=(',', ':')) + '\n')
    result = {'normalizer': counts, 'accepted_examples': list(positives)}
    (ROOT / 'audit_results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
