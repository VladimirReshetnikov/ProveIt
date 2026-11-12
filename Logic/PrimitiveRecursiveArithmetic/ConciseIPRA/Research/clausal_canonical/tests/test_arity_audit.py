"""Independent named-variable opening oracle and certificate boundary checks.

This is a test utility, not part of either trusted checker.
"""
import copy
import importlib.util
import json
import pathlib
import random

ROOT = pathlib.Path(__file__).resolve().parents[1]
PACKAGE = ROOT


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


NEW = load(PACKAGE / 'code/arity_checker.py', 'arity_new')
OLD = load(PACKAGE / 'comparison/arity_current_control.py', 'arity_old')
RNG = random.Random(20261112)


def decode(tree, env, prefix, serial):
    """Convert to explicit named binders; array arities become distinct tags."""
    if type(tree) is int:
        if tree == 0:
            return ('zero',)
        if tree < 0:
            return ('free', -tree)
        return ('var', env[tree - 1])
    if len(tree) == 3:
        name = prefix + str(next(serial))
        return ('rec', name, decode(tree[0], env, prefix, serial),
                decode(tree[1], env, prefix, serial),
                decode(tree[2], [name] + env, prefix, serial))
    if len(tree) == 1:
        x, y = prefix + str(next(serial)), prefix + str(next(serial))
        return ('D', x, y, decode(tree[0], [y, x] + env, prefix, serial))
    if tree[0] == 'Q':
        y = prefix + str(next(serial))
        return ('Q', y, decode(tree[1], [y] + env, prefix, serial))
    return ('eq', decode(tree[0], env, prefix, serial),
            decode(tree[1], env, prefix, serial))


def replace_named(tree, target, image):
    if tree[0] == 'var':
        return image if tree[1] == target else tree
    if tree[0] in ('zero', 'free'):
        return tree
    if tree[0] == 'rec':
        n = replace_named(tree[2], target, image)
        a = replace_named(tree[3], target, image)
        # Canonicalize before visiting a body which may have become dead.
        h = ('zero',) if n == ('zero',) else replace_named(tree[4], target, image)
        return ('rec', tree[1], n, a, h)
    if tree[0] == 'D':
        return ('D', tree[1], tree[2], replace_named(tree[3], target, image))
    if tree[0] == 'Q':
        return ('Q', tree[1], replace_named(tree[2], target, image))
    return ('eq', replace_named(tree[1], target, image),
            replace_named(tree[2], target, image))


def encode(tree, env):
    tag = tree[0]
    if tag == 'zero':
        return 0
    if tag == 'free':
        return -tree[1]
    if tag == 'var':
        return env.index(tree[1]) + 1
    if tag == 'rec':
        return [encode(tree[2], env), encode(tree[3], env),
                encode(tree[4], [tree[1]] + env)]
    if tag == 'D':
        return [encode(tree[3], [tree[2], tree[1]] + env)]
    if tag == 'Q':
        return ['Q', encode(tree[2], [tree[1]] + env)]
    return [encode(tree[1], env), encode(tree[2], env)]


def oracle(tree, image, ambient_depth, protected_depth):
    import itertools
    names = ['outer' + str(i) for i in range(ambient_depth)]
    source = decode(tree, names, 's', itertools.count())
    value = decode(image, [], 'v', itertools.count())
    result = replace_named(source, names[protected_depth], value)
    return encode(result, names[:protected_depth] + names[protected_depth + 1:])


def random_term(scope, depth, height):
    if height == 0 or RNG.random() < .58:
        return RNG.choice(list(range(-scope, depth + 1)))
    n = random_term(scope, depth, height - 1)
    a = random_term(scope, depth, height - 1)
    h = random_term(scope, depth + 1, height - 1)
    return [n, a, 0 if n == 0 else h]


def random_formula(scope, depth, height, q=False):
    choice = RNG.random()
    if height and choice < .3:
        return [random_formula(scope, depth + 2, height - 1, q)]
    if q and height and choice < .5:
        return ['Q', random_formula(scope, depth + 1, height - 1, q)]
    return [random_term(scope, depth, 3), random_term(scope, depth, 3)]


def accepted(module, certificate):
    try:
        return module.verify(copy.deepcopy(certificate)) is True
    except Exception:
        return False


def rzero(a=0):
    return ['r', 0, 0, a]


def refl(a, old=False):
    return ['x', [1, a] if old else 1, rzero(a), rzero(a)]


S = lambda a: [0, a, 0]
H = [[[0, 0, 0], 0, 0], 0]


def corpus(old=False):
    dyy = [[1, 1]]
    dyy_proof = ['i', dyy, 0, refl(S(-1), old)]
    dconst = [[0, 0]]
    fact_use = ['h', 0] if old else ['u', 0, 0, rzero()]
    dconst_proof = ['i', dconst, 0, fact_use]
    closure_use = (['q', S(0), ['h', 0], refl(0, True)] if old
                   else ['u', 0, S(0), refl(0)])
    dxx = [[2, 2]]
    dxx_proof = ['i', dxx, 0, refl(0, old)]
    old_clause_use = (['q', 0, ['h', 0], refl(-1, True)] if old
                      else ['u', 0, 0, refl(-1)])
    discard_equality = ['x', [0, 0] if old else 0,
                        old_clause_use, refl(0, old)]
    nested = ['e', [0, 0], dxx_proof,
              ['e', [0, 0], ['i', dxx, -1, refl(-1, old)], discard_equality]]
    return [
        ('computation', {'goal': H, 'proof': rzero()}),
        ('reflexivity', {'goal': [0, 0], 'proof': refl(0, old)}),
        ('atomic_progress', {'goal': dyy, 'proof': dyy_proof}),
        ('ordinary_assumption', {'goal': dconst, 'proof': dconst_proof}),
        ('paired_elimination', {'goal': [S(0), S(0)],
                                'proof': ['e', [S(0), S(0)], dyy_proof, closure_use]}),
        ('compound_cases', {'goal': [dconst],
                            'proof': ['i', [dconst], 0, fact_use]}),
        ('witness_opening', {'goal': [0, 0],
                            'proof': ['e', [0, 0], dxx_proof, discard_equality]}),
        ('nested_scope_retains_old_parameter', {'goal': [0, 0], 'proof': nested}),
    ]


def main():
    opening_counts = {}
    for module, label, allow_q in [(NEW, 'new', False), (OLD, 'control', True)]:
        count = 0
        for is_formula in (False, True):
            for _ in range(3000):
                scope, ambient = RNG.randrange(4), RNG.randrange(1, 5)
                protected = RNG.randrange(ambient)
                image = random_term(scope, 0, 3)
                tree = (random_formula(scope, ambient, 3, allow_q) if is_formula
                        else random_term(scope, ambient, 3))
                validator = module.formula if is_formula else module.term
                assert validator(tree, scope, ambient)
                assert module.term(image, scope)
                actual = module.opening(tree, image, protected)
                expected = oracle(tree, image, ambient, protected)
                assert actual == expected, (label, tree, image, protected, actual, expected)
                assert validator(actual, scope, ambient - 1)
                count += 1
        opening_counts[label] = count

    # Targeted capture and normalization examples, independent of the RNG.
    assert NEW.opening([1, -1, 1], 0) == [0, -1, 0]
    assert NEW.opening([[3, 1]], [-1, 0, 1]) == [[[-1, 0, 1], 1]]
    assert NEW.opening([[2, 1]], [-1, 0, 1], 1) == [[2, 1]]

    positive = {}
    for module, label in [(NEW, 'new'), (OLD, 'control')]:
        cases = corpus(module is OLD)
        for name, certificate in cases:
            assert accepted(module, certificate), (label, name)
        positive[label] = [name for name, _ in cases]

    invalid = []
    def bad(name, goal, proof):
        invalid.append((name, {'goal': goal, 'proof': proof}))
    for value, name in [(False, 'false'), (True, 'true'), (0.0, 'float'),
                        ('0', 'string'), (None, 'null'), ([], 'empty'),
                        ([0, 0, 0, 0], 'arity4'), ([0], 'formula_as_term')]:
        bad('goal_' + name, [value, value], refl(0))
        bad('computation_' + name, H, ['r', value, 0, 0])
    bad('positive_free_goal', [1, 1], refl(0))
    bad('future_free_goal', [-1, -1], refl(0))
    bad('positive_counter', H, ['r', 1, 0, 0])
    bad('future_counter', H, ['r', -1, 0, 0])
    bad('body_out_of_scope', H, ['r', 0, 0, 2])
    bad('body_bool_erased', H, ['r', [0, 0, False], 0, 0])
    bad('noncanonical_zero_body', H, ['r', [0, 0, 1], 0, 0])
    bad('transport_template_scope', [0, 0], ['x', 2, rzero(), rzero()])
    bad('transport_minor_mismatch', [0, 0], ['x', 0, rzero(), rzero()])
    bad('positive_DI_witness', [[0, 0]], ['i', [[0, 0]], 1, refl(0)])
    bad('future_DI_witness', [[0, 0]], ['i', [[0, 0]], -1, refl(0)])
    bad('wrong_progress_target', [[1, 0]], ['i', [[1, 0]], 0, ['u', 0, 0, rzero()]])
    bad('use_bool_index', [[0, 0]], ['i', [[0, 0]], 0, ['u', False, 0, rzero()]])
    bad('use_negative_index', [[0, 0]], ['i', [[0, 0]], 0, ['u', -1, 0, rzero()]])
    bad('use_missing_index', [[0, 0]], ['i', [[0, 0]], 0, ['u', 1, 0, rzero()]])
    bad('use_positive_target', [[0, 0]], ['i', [[0, 0]], 0, ['u', 0, 1, rzero()]])
    bad('use_future_target', [[0, 0]], ['i', [[0, 0]], 0, ['u', 0, -2, rzero()]])
    bad('use_wrong_base', [[0, 0]], ['i', [[0, 0]], 0, ['u', 0, 0, refl(0)]])
    bad('forged_hyp_rule', [[0, 0]], ['i', [[0, 0]], 0, ['h', 0]])
    bad('DE_eigen_escape', [-1, -1], ['e', [-1, -1], corpus()[2][1]['proof'], refl(-1)])
    bad('nested_future_goal', [[0, 0]], ['i', [[0, 0]], 0,
        ['e', [-2, -2], corpus()[2][1]['proof'], refl(-2)]])
    bad('empty_proof', [0, 0], [])
    bad('unknown_rule', [0, 0], ['run', 'anything'])
    bad('Q_not_public', ['Q', [0, 0]], refl(0))
    for name, certificate in invalid:
        assert not accepted(NEW, certificate), name
    extra = dict(corpus()[0][1], scope=100)
    assert not accepted(NEW, extra)
    assert not accepted(NEW, [H, rzero()])

    result = {'opening_vs_independent_named_oracle': opening_counts,
              'targeted_opening_checks': 3,
              'positive_certificates': positive,
              'rejected_primary_certificates': [name for name, _ in invalid]
                  + ['extra_top_level_key', 'non_object_top_level'],
              'status': 'PASS',
              'limits': 'Finite executable checks; not a formal soundness proof.'}
    target = PACKAGE / 'evidence/arity_audit_results.json'
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
