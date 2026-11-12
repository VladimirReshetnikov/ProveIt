"""Finite counterinterpretation to zero-source-only native transport.

The native equation symbol is interpreted as R, not metatheoretic equality.
This is a counterinterpretation of the proposed weakened proof rules, not an
ordinary equality model of iPRA. The universal argument is in the report.
"""
import itertools
import json

DOMAIN = (0, 1)


def successor(number):
    return 1


def iterate(counter, seed, update):
    return 1


def equation(left, right):
    return left == 1


def implies(left, right):
    return not left or right


def closure(row):
    return implies(row[0], all(row))


updates = list(itertools.product(DOMAIN, repeat=2))
computations = 0
for seed, update in itertools.product(DOMAIN, updates):
    assert equation(iterate(0, seed, update), seed)
    computations += 1
    for n in DOMAIN:
        assert equation(iterate(successor(n), seed, update),
                        update[iterate(n, seed, update)])
        computations += 1

matrices = list(itertools.product((False, True), repeat=4))
introductions = eliminations = 0
for bits in matrices:
    rows = (bits[:2], bits[2:])
    paired = any(closure(row) for row in rows)
    for witness in DOMAIN:
        row = rows[witness]
        cases = all(implies(row[0], row[successor(n)]) for n in DOMAIN)
        progress = all(implies(row[n], row[successor(n)]) for n in DOMAIN)
        assert implies(cases, paired)
        assert implies(progress, paired)
        introductions += 2
    for conclusion in (False, True):
        continuation = all(implies(closure(row), conclusion) for row in rows)
        assert implies(paired and continuation, conclusion)
        eliminations += 1

# All zero-source major premises are false, for every target value.
assert all(not equation(0, target) for target in DOMAIN)
# The original arbitrary-source transport would infer a false conclusion:
# H: I(0,0;u.0)=0; F(v): v=0; H is both major and minor.
assert equation(iterate(0, 0, (0, 0)), 0)
assert not equation(0, 0)
print(json.dumps({'domain_size': 2, 'computation_instances': computations,
                  'introduction_checks': introductions,
                  'elimination_checks': eliminations,
                  'reflexivity_at_zero': equation(0, 0)}, sort_keys=True))
