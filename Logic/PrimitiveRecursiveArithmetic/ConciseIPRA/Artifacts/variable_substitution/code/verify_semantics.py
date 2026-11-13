"""Independent bounded semantics tests for scalar I binding operations.

Run beside scalar_latest.py.  These regression checks are not a formal proof of
normalization or of equivalence with iPRA.  The evaluator below does not call
the candidate's normalizer, substitution, or shifting implementation.
"""
import json
import random

import scalar_latest as candidate


RANDOM_SEED = 314159
TRIALS = 200
rng = random.Random(RANDOM_SEED)


def evaluate(term, environment, budget=None):
    """Standard natural-number semantics; nearest binder is environment[0]."""
    if budget is None:
        budget = [50000]
    budget[0] -= 1
    if budget[0] < 0:
        raise OverflowError('Semantic evaluation budget exhausted')
    tag = term[0]
    if tag == 'z':
        return 0
    if tag == 'v':
        return environment[term[1]]
    if tag == 's':
        return evaluate(term[1], environment, budget) + 1
    if tag != 'i':
        raise ValueError('Not a numerical term')
    counter = evaluate(term[1], environment, budget)
    accumulator = evaluate(term[2], environment, budget)
    if counter > budget[0]:
        raise OverflowError('Iteration budget exhausted')
    for _ in range(counter):
        accumulator = evaluate(term[3], [accumulator] + environment, budget)
    return accumulator


def scoped(term, variables):
    """Independent grammar and de Bruijn scope validation."""
    if type(term) is not list or not term:
        return False
    if term[0] == 'z':
        return len(term) == 1
    if term[0] == 'v':
        return (len(term) == 2 and type(term[1]) is int
                and 0 <= term[1] < variables)
    if term[0] == 's':
        return len(term) == 2 and scoped(term[1], variables)
    return (term[0] == 'i' and len(term) == 4
            and scoped(term[1], variables)
            and scoped(term[2], variables)
            and scoped(term[3], variables + 1))


def generate(variables, depth):
    if depth == 0 or rng.randrange(4) == 0:
        return ['v', rng.randrange(variables)] if variables and rng.randrange(2) else ['z']
    if rng.randrange(3) == 0:
        return ['s', generate(variables, depth - 1)]
    return ['i', generate(variables, depth - 1),
            generate(variables, depth - 1),
            generate(variables + 1, depth - 1)]


def normalize(term):
    return candidate.walk(term, lambda index, depth: ['v', index])


def check_result(term, variables, environment, expected):
    assert scoped(term, variables), ('ill-scoped result', term, variables)
    candidate.syntax(term, variables)
    actual = evaluate(term, environment)
    assert actual == expected, ('wrong value', term, environment, expected, actual)


counts = dict(normalization=0, substitution_drop_0=0,
              substitution_drop_1=0, shifting=0, explicit_capture=0)

for trial in range(TRIALS):
    variables = rng.randrange(1, 6)
    environment = [rng.randrange(4) for _ in range(variables)]
    source = generate(variables, 3 + trial % 2)
    normal = normalize(source)
    check_result(normal, variables, environment, evaluate(source, environment))
    counts['normalization'] += 1

    index = rng.randrange(variables)
    replacement = normalize(generate(variables, 3))
    changed = environment.copy()
    changed[index] = evaluate(replacement, environment)
    result = candidate.sub(normal, replacement, drop=0, index=index)
    check_result(result, variables, environment, evaluate(source, changed))
    counts['substitution_drop_0'] += 1

    source_with_extra = generate(variables + 1, 3 + trial % 2)
    index = rng.randrange(variables + 1)
    inserted = environment.copy()
    inserted.insert(index, evaluate(replacement, environment))
    result = candidate.sub(normalize(source_with_extra), replacement,
                           drop=1, index=index)
    check_result(result, variables, environment,
                 evaluate(source_with_extra, inserted))
    counts['substitution_drop_1'] += 1

    cutoff = rng.randrange(variables + 1)
    amount = rng.randrange(1, 4)
    extended = (environment[:cutoff] + [rng.randrange(4) for _ in range(amount)]
                + environment[cutoff:])
    result = candidate.shift(normal, amount, cutoff)
    check_result(result, variables + amount, extended,
                 evaluate(source, environment))
    counts['shifting'] += 1

# Outer replacement v0 must remain an outer parameter inside *two* iterator
# bodies, while each body's accumulator remains its own distinct variable.
nested = ['i', ['v', 0], ['v', 1],
          ['i', ['v', 1], ['v', 0], ['s', ['v', 2]]]]
for drop in (0, 1):
    for index in (0, 1):
        environment = [2, 3] if drop == 0 else [2]
        replacement = ['s', ['v', 0]]
        replacement_value = evaluate(replacement, environment)
        original_environment = environment.copy()
        if drop:
            original_environment.insert(index, replacement_value)
        else:
            original_environment[index] = replacement_value
        result = candidate.sub(normalize(nested), replacement, drop, index)
        check_result(result, len(environment), environment,
                     evaluate(nested, original_environment))
        counts['explicit_capture'] += 1

print(json.dumps({
    'candidate': 'scalar_latest.py',
    'random_seed': RANDOM_SEED,
    'random_trials': TRIALS,
    'checks': counts,
    'passed': sum(counts.values()),
    'failed': 0,
    'resource_skipped': 0,
    'scope': ('Independent standard-N semantics of scalar-I normalization, '
              'arbitrary-index substitution with drop 0 and 1, and shifting; '
              'generated terms include nested iterator binders.'),
    'limitation': 'Finite regression checks, not a formal proof.'
}, indent=2))
