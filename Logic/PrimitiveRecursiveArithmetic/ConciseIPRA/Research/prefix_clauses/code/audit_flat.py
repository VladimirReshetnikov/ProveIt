"""Independent semantic and scope audit; not a trusted proof component."""
import importlib.util
import hashlib
import json
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECKER = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else HERE / 'flat_control.py'
spec = importlib.util.spec_from_file_location('flat_checker_under_audit', CHECKER)
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
rng = random.Random(1471604)


def numeral(n):
    return 0 if not n else [numeral(n - 1)]


def random_term(scope, depth, fuel=3):
    leaves = list(range(-scope, depth + 1))
    if fuel == 0 or rng.randrange(4) == 0:
        return rng.choice(leaves)
    if rng.randrange(2):
        return [random_term(scope, depth, fuel - 1)]
    # Small literal counters keep this test independent of runtime growth.
    return [numeral(rng.randrange(3)), random_term(scope, depth, fuel - 1),
            random_term(scope, depth + 1, fuel - 1)]


def value(term, free, bound=()):
    """Environment semantics; no syntactic substitution is used here."""
    if type(term) is int:
        return 0 if term == 0 else free[-term - 1] if term < 0 else bound[term - 1]
    if len(term) == 1:
        return value(term[0], free, bound) + 1
    count = value(term[0], free, bound)
    state = value(term[1], free, bound)
    for _ in range(count):
        state = value(term[2], free, (state,) + bound)
    return state


def formula_value(formula, free, outer=(), extent=3):
    """Finite D semantics used solely to compare formula substitutions."""
    depth, left, right = formula

    def recurse(k, bound):
        if k == 0:
            return value(left, free, bound) == value(right, free, bound)
        for x in range(extent):
            if (not recurse(k - 1, (0, x) + bound)
                    or all(recurse(k - 1, (y, x) + bound) for y in range(extent))):
                return True
        return False

    return recurse(depth, outer)


counts = {'outer_matrix_opening': 0, 'outer_witness_opening': 0,
          'successor_eval_binding': 0, 'adversarial_rejections': 0,
          'accepted_examples': 0}

for _ in range(400):
    scope, k = rng.randrange(4), rng.randrange(3)
    free = tuple(rng.randrange(4) for _ in range(scope))
    witness = random_term(scope, 0, 2)
    result_value = value(witness, free)
    body = [k, random_term(scope, 2 * k + 1), random_term(scope, 2 * k + 1)]
    opened = checker.opening(body, witness)
    assert checker.formula(opened, scope)
    assert formula_value(opened, free) == formula_value(body, free, (result_value,))
    inner_values = tuple(rng.randrange(4) for _ in range(2 * k))
    for i in (1, 2):
        assert value(opened[i], free, inner_values) == value(body[i], free, inner_values + (result_value,))
    counts['outer_matrix_opening'] += 1

    body = [k, random_term(scope, 2 * k + 2), random_term(scope, 2 * k + 2)]
    opened = checker.opening(body, witness, 1)
    y = rng.randrange(4)
    assert formula_value(opened, free, (y,)) == formula_value(body, free, (y, result_value))
    for i in (1, 2):
        assert value(opened[i], free, inner_values + (y,)) == value(body[i], free, inner_values + (y, result_value))
    counts['outer_witness_opening'] += 1

for _ in range(300):
    scope = rng.randrange(4)
    free = tuple(rng.randrange(4) for _ in range(scope))
    body = random_term(scope, 1, 4)
    previous = random_term(scope, 0, 3)
    result = checker.sub(body, previous)
    assert checker.term(result, scope)
    assert value(result, free) == value(body, free, (value(previous, free),))
    counts['successor_eval_binding'] += 1


def refl(t):
    return ['u', 0, t, None]


def accepted(goal, proof):
    checker.verify({'goal': goal, 'proof': proof})
    counts['accepted_examples'] += 1


def rejected(data):
    try:
        checker.verify(data)
    except Exception:
        counts['adversarial_rejections'] += 1
        return
    raise AssertionError('unsound or out-of-contract acceptance: ' + repr(data))


accepted([0, 0, 0], refl(0))
one, two = numeral(1), numeral(2)
closed_body = [one, 1, [2]]  # I(1,u;v.Su); the inner 2 refers to outer u.
counter, seed = two, 0
previous = [counter, seed, closed_body]
later = [[counter], seed, closed_body]
successor_proof = ['v', refl(previous), refl(later)]
successor_goal = [0, later, checker.sub(closed_body, previous)]
accepted(successor_goal, successor_proof)
assert formula_value(successor_goal, ())

# A genuine D theorem, used for escape attacks below.
major_goal = [1, 2, 2]
major = ['i', major_goal, 0, refl(0)]
accepted(major_goal, major)

# The literal-reflexive-leaf optimization legitimately skips a compound base.
compound_goal = [2, 4, 4]
compound = ['i', compound_goal, one, ['i', [1, one, one], one, refl(one)]]
accepted(compound_goal, compound)
compound_major_goal = [2, 0, 0]
compound_major = ['i', compound_major_goal, one, ['i', [1, 0, 0], one, refl(0)]]
accepted([1, 0, 0], ['e', compound_major, ['u', 1, 0, None]])

bad_data = [
    {'goal': [0, 0, one], 'proof': refl(0)},
    {'goal': [0, 0, 0], 'proof': refl(-1)},
    {'goal': [0, 0, 0], 'proof': refl(1)},
    {'goal': [0, 0, 0], 'proof': refl(False)},
    {'goal': [0, 0, 0], 'proof': refl(0.0)},
    {'goal': [True, 0, 0], 'proof': refl(0)},
    {'goal': [0, 0, 0], 'proof': ['u', -1, 0, None]},
    {'goal': [0, 0, 0], 'proof': ['u', True, 0, None]},
    {'goal': [0, 0, 0], 'proof': ['u', 1, 0, None]},
    {'goal': [0, 0, 0], 'proof': ['e', major, refl(-1)]},
    # Escape is rejected even in a dead zero-iterator body.
    {'goal': [0, 0, 0], 'proof': ['e', major, refl([0, 0, -1])]},
    # Escape hidden below a D binder.
    {'goal': major_goal, 'proof': ['e', major, ['i', [1, -1, -1], 0, refl(-1)]]},
    {'goal': major_goal, 'proof': ['i', major_goal, -1, refl(0)]},
    {'goal': major_goal, 'proof': ['i', major_goal, 1, refl(0)]},
    {'goal': [0, 0, 0], 'proof': ['e', refl(0), refl(0)]},
    {'goal': [0, 0, 0], 'proof': ['v', major, refl(0)]},
    {'goal': [0, 0, 0], 'proof': ['v', refl(0), refl(0)]},
    {'goal': [0, 0, 0], 'proof': ['v', refl(0), refl([one, one, 1])]},
    {'goal': [0, 0, 0], 'proof': ['i', [1, 3, 3], 0, refl(0)]},
    {'goal': [0, 0, 0], 'proof': refl(0), 'extra': 1},
]
for data in bad_data:
    rejected(data)

report = {
    'result': 'PASS', 'checker': CHECKER.name,
    'checker_sha256': hashlib.sha256(CHECKER.read_bytes()).hexdigest(),
    'seed': 1471604,
    'checks': counts,
    'method': 'Independent environment semantics, plus public-interface scope and shape attacks.',
    'limits': 'Finite checks supplement the written proof; they do not establish universal soundness or bi-interpretability.'
}
(HERE / 'flat_audit_results.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
