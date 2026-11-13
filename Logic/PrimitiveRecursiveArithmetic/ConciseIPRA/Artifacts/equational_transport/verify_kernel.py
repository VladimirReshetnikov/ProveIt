"""Focused primitive-rule and whole-program tests; not an equivalence proof."""
from pathlib import Path
import importlib.util
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'code' / (name + '.py'))
    loaded = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(loaded)
    return loaded

K = module('crossed_back')
E = module('equation_back')

def H(index):
    return ['u', index, None]

def R(term, count):
    return ['a', term, H(count)]

def xback(term, major, minor):
    return ['v', term, major, minor]

def eq_to_crossed(proof):
    tag, *args = proof
    if tag == 'v':
        goal, major, minor = args
        left, right = goal
        translated_major = eq_to_crossed(major)
        translated_minor = eq_to_crossed(minor)
        first = xback(left, translated_major, translated_minor)
        return xback(right, translated_major, first)
    if tag == 'u':
        index, premise = args
        return [tag, index, eq_to_crossed(premise) if isinstance(premise, list) else premise]
    if tag == 'c':
        return proof
    if tag == 'a':
        term, branch = args
        return [tag, term, eq_to_crossed(branch)]
    if tag == 'e':
        goal, major, branch = args
        return [tag, goal, eq_to_crossed(major), eq_to_crossed(branch)]
    if tag == 'i':
        goal, branch = args
        return [tag, goal, eq_to_crossed(branch)]
    raise ValueError(tag)

context = [([], [-1, 0])]
primitive = [
    ('primitive_symmetry', context, 1, xback(-1, H(0), R(0, 1)), [0, -1]),
    ('successor_congruence', context, 1, xback([0, -1], H(0), R([0, 0], 1)), [[0, 0], [0, -1]]),
    ('constant_term', context, 1, xback(0, H(0), R(0, 1)), [0, 0]),
    ('self_containing_replacement', [([], [-1, [0, -1]])], 1,
     xback(-1, H(0), R([0, -1], 1)), [[0, -1], -1]),
]
for name, g, n, proof, expected in primitive:
    actual = K.derive(proof, g, n)
    assert actual == expected, (name, actual, expected)

# Every case is a legal atomic Back proof. The compiler uses exactly two
# crossed steps per Back and otherwise retains every existing scope.
simulations = [
    ('eqback_reflexivity', context, 1, ['v', [-1, -1], H(0), R(0, 1)]),
    ('eqback_successor', context, 1, ['v', [[0, -1], [0, -1]], H(0), R([0, 0], 1)]),
    ('eqback_constant_left', context, 1, ['v', [0, -1], H(0), R(0, 1)]),
    ('eqback_constant_right', context, 1, ['v', [-1, 0], H(0), R(0, 1)]),
    ('eqback_self_containing', [([], [-1, [0, -1]])], 1,
     ['v', [-1, -1], H(0), R([0, -1], 1)]),
]
for name, g, n, proof in simulations:
    actual = E.derive(proof, g, n)
    transformed = K.derive(eq_to_crossed(proof), g, n)
    assert actual == transformed, (name, actual, transformed)

zero = {'goal': [0, 0], 'proof': ['a', 0, xback(-1, H(0), R(0, 1))]}
one = {'goal': [[0, 0], [0, 0]], 'proof': R([0, 0], 0)}
cases = [
    ('closed_crossed_symmetry', zero, True),
    ('closed_successor_reflexivity', one, True),
    ('forged_goal', dict(zero, goal=[0, [0, 0]]), False),
    ('compound_template', {'goal': [0, 0], 'proof': ['a', 0, xback([[0, 0]], H(0), R(0, 1))]}, False),
    ('repaired_successor_tag', {'goal': [0, 0], 'proof': ['a', 0, xback([-1, 0], H(0), R([0, 0], 1))]}, False),
    ('old_source', {'goal': [0, 0], 'proof': ['a', 0, ['a', 0, xback(-1, H(0), R(0, 2))]]}, False),
    ('zero_source', {'goal': [0, 0], 'proof': xback(0, R(0, 0), R(0, 0))}, False),
    ('wrong_minor', {'goal': [0, 0], 'proof': ['a', 0, xback([0, -1], H(0), R(0, 1))]}, False),
    ('boolean_term', {'goal': [0, 0], 'proof': ['a', 0, xback(False, H(0), R(0, 1))]}, False),
    ('future_parameter', {'goal': [0, 0], 'proof': ['a', 0, xback(-2, H(0), R(0, 1))]}, False),
    ('free_public_goal', {'goal': [-1, -1], 'proof': R(-1, 0)}, False),
    ('extra_public_field', dict(zero, ignored=True), False),
]
fixtures = ROOT / 'tests' / 'kernel_fixtures'
fixtures.mkdir(exist_ok=True)
receipt = []
for name, data, expected in cases:
    path = fixtures / (name + '.json')
    path.write_text(json.dumps(data, separators=(',', ':')) + '\n')
    for optimized in (False, True):
        command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / 'code' / 'crossed_back.py')]
        process = subprocess.run(command, input=path.read_bytes(), capture_output=True, timeout=20)
        accepted = process.returncode == 0 and process.stdout == b'ACCEPT\n'
        assert accepted == expected, (name, optimized, process.stdout, process.stderr)
        receipt.append(dict(name=name, optimized=optimized, accepted=accepted, expected=expected))
summary = dict(primitive_cases=len(primitive), atomic_back_simulations=len(simulations),
               subprocess_cases=len(receipt), failures=0, results=receipt,
               limitation='Finite checks support code review. They do not prove full iPRA consequence equivalence.')
(ROOT / 'evidence' / 'kernel_validation.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k != 'results'}, indent=2))
