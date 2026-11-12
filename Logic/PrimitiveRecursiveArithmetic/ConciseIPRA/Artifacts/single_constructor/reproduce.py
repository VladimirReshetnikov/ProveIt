"""Finite implementation checks; these are not a proof of equivalence with iPRA.

Run from any directory with Python 3.12. Uses only the standard library.
The source calculus and source certificates are pinned upstream files.
"""
import ast
from copy import deepcopy
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


native = module('native', ROOT / 'reference/inferred_witness/code/checker.py')
new = module('counter_recursion', ROOT / 'code/checker.py')


def S(a):
    return [0, a, 0]


def P(a):
    return [a, 0, 2]


def normal(a):
    return new.walk(a, lambda i, d: i)


def lift(a, count):
    return new.walk(a, lambda i, d: i + count if i > d else i)


def rec(n, seed, body):
    """Ordinary counter-aware primitive recursion; body binds u=1 and i=2."""
    step = new.walk(body, lambda i, d: lift(P(1), d) if i == d + 1 else i)
    return normal(P([n, seed, S(step)]))


def add(n, a):
    return rec(n, a, S(1))


def multiply(n, a):
    return rec(n, 0, add(lift(a, 2), 1))


def numeral(n):
    result = 0
    for _ in range(n):
        result = S(result)
    return result


def term(a, env=(), shift=0):
    """Native I -> P(R(n,a;i,u.S(h(P(u))))), with explicit binding.

    env maps source bound variables to target terms. shift counts the extra
    target binders affecting all source variables outside env.
    """
    if type(a) is int:
        if a <= 0:
            return a
        return env[a - 1] if a <= len(env) else a + shift
    if len(a) == 2:
        if a[0] != 0:
            raise ValueError('invalid source successor')
        return S(term(a[1], env, shift))
    if len(a) != 3:
        raise ValueError('invalid source term')
    n, seed, body = a
    body_env = (P(1),) + tuple(lift(t, 2) for t in env)
    step = S(term(body, body_env, shift + 1))
    return normal(P([term(n, env, shift), term(seed, env, shift), step]))


def formula(a, env=(), shift=0):
    if len(a) == 2:
        return normal([term(t, env, shift) for t in a])
    if len(a) != 1:
        raise ValueError('invalid source formula')
    body_env = (1, 2) + tuple(lift(t, 2) for t in env)
    return [formula(a[0], body_env, shift)]


def proof(p):
    if p is None:
        return None
    match p:
        case ['u', j, t, q]:
            return ['u', j, term(t), proof(q)]
        case ['i', body, t, branch]:
            return ['i', formula(body, (1, 2)), term(t), proof(branch)]
        case ['e', major, branch]:
            return ['e', proof(major), proof(branch)]
    raise ValueError('invalid source proof')


def certificate(data):
    return {'goal': formula(data['goal']), 'proof': proof(data['proof'])}


def value(a, env=(), params=None, seeded=True):
    """Independent natural-number evaluator; intentionally has no rewriting."""
    if params is None:
        params = {-1: 1, -2: 2}
    if type(a) is int:
        return 0 if a == 0 else env[a - 1] if a > 0 else params[a]
    if not seeded and len(a) == 2:
        return 1 + value(a[1], env, params, False)
    n = value(a[0], env, params, seeded)
    result = value(a[1], env, params, seeded) + int(seeded)
    if n > 30:
        raise OverflowError('evaluation cutoff')
    for i in range(n):
        body_env = (result, i) + tuple(env) if seeded else (result,) + tuple(env)
        result = value(a[2], body_env, params, seeded)
        if result > 100:
            raise OverflowError('evaluation cutoff')
    return result


def random_term(rng, depth, bound, seeded=True):
    if depth == 0 or rng.randrange(3) == 0:
        return rng.choice([0, -1, -2] + list(range(1, bound + 1)))
    if not seeded and rng.randrange(4) == 0:
        return [0, random_term(rng, depth - 1, bound, False)]
    return [random_term(rng, depth - 1, bound, seeded),
            random_term(rng, depth - 1, bound, seeded),
            random_term(rng, depth - 1, bound + (2 if seeded else 1), seeded)]


def acceptance(checker, data):
    try:
        checker.check(deepcopy(data))
        return True
    except (AssertionError, ValueError, TypeError, IndexError, KeyError, RecursionError):
        return False


def metric(path):
    text = ast.unparse(ast.parse(path.read_text())) + '\n'
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = [t for t in tokenize.generate_tokens(io.StringIO(text).readline)
              if t.type not in ignored]
    return {'normalized_bytes': len(text.encode()), 'tokens': len(tokens),
            'ast_nodes': len(list(ast.walk(ast.parse(text)))),
            'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def main():
    examples = ROOT / 'code/examples'
    examples.mkdir(exist_ok=True)
    positives = {}
    for path in sorted((ROOT / 'reference/inferred_witness/code/examples').glob('*.json')):
        source = json.loads(path.read_text())
        assert acceptance(native, source), path.name
        data = certificate(source)
        assert acceptance(new, data), path.name
        positives[path.name] = data

    # Genuine use of the induction hypothesis for I(y,0;u.Su)=y.
    # Native proof constructors are untrusted; both checkers inspect the result.
    sys.modules['checker'] = native
    helpers = module('proof_tools', ROOT / 'reference/inferred_witness/code/proof_tools.py')
    y = helpers.Y
    body = [helpers.I(y, 0, helpers.U, helpers.S(helpers.U)), y]
    goal = helpers.D(body)
    eq = helpers.at(body, y, -1)
    local = helpers.INITIAL + [([], eq)]
    step = helpers.crossed_transport(helpers.use(1, 0),
                                    helpers.refl(helpers.S(eq[0])),
                                    helpers.S(helpers.V), helpers.V, local)
    source = {'goal': goal, 'proof': ['i', goal[0], 0, step]}
    assert acceptance(native, source)
    positives['used_equation_induction.json'] = certificate(source)
    assert acceptance(new, positives['used_equation_induction.json'])
    (ROOT / 'evidence/used_equation_induction_native.json').write_text(json.dumps(source, indent=2) + '\n')

    for name, data in positives.items():
        (examples / name).write_text(json.dumps(data, indent=2) + '\n')

    # Negative controls target actual checker obligations rather than fuzz counts.
    refl0 = {'goal': [0, 0], 'proof': ['u', 0, 0, None]}
    negatives = {
        'false_equation': {'goal': [0, S(0)], 'proof': ['u', 0, 0, None]},
        'boolean_clause': {'goal': [0, 0], 'proof': ['u', False, 0, None]},
        'negative_clause': {'goal': [0, 0], 'proof': ['u', -1, 0, None]},
        'missing_clause': {'goal': [0, 0], 'proof': ['u', 1, 0, None]},
        'boolean_term': {'goal': [0, 0], 'proof': ['u', 0, False, None]},
        'float_term': {'goal': [0, 0], 'proof': ['u', 0, 0.0, None]},
        'old_successor_shape': {'goal': [[0, 0], [0, 0]], 'proof': ['u', 0, [0, 0], None]},
        'free_term': {'goal': [0, 0], 'proof': ['u', 0, 1, None]},
        'escaping_parameter': {'goal': [-1, -1], 'proof': ['u', 0, -1, None]},
        'noncanonical_zero_body': {'goal': [[0, 0, 1], [0, 0, 1]], 'proof': ['u', 0, [0, 0, 1], None]},
        'successor_redex': {'goal': [[S(0), 0, 2], [S(0), 0, 2]], 'proof': ['u', 0, [S(0), 0, 2], None]},
        'hidden_unbound_variable': {'goal': [0, 0], 'proof': ['u', 0, [0, 0, 7], None]},
        'wrong_progress_step': {'goal': [[1, 1]], 'proof': ['i', [1, 1], 0, ['u', 1, 0, None]]},
        'local_clause_in_major': {'goal': [0, 0], 'proof': ['e', ['u', 1, 0, None], ['u', 0, 0, None]]},
        'equation_as_open_major': {'goal': [0, 0], 'proof': ['e', ['u', 0, 0, None], ['u', 0, 0, None]]},
        'unknown_rule': {'goal': [0, 0], 'proof': ['axiom', [0, 0]]},
        'extra_document_key': dict(refl0, extra=0),
    }
    for path in sorted((ROOT / 'reference/inferred_witness/code/reject_examples').glob('*.json')):
        source = json.loads(path.read_text())
        assert not acceptance(native, source), path.name
        # Compilation is defined on valid source syntax. It may repair an
        # invalid erased subterm, so that malformed-syntax case is not a
        # rejection-preservation claim. New raw malformed cases are above.
        if path.stem == 'erased_invalid_intro_matrix':
            continue
        try:
            negatives['translated_' + path.stem] = certificate(source)
        except (ValueError, TypeError, IndexError):
            pass
    for name, data in negatives.items():
        assert not acceptance(new, data), name
    (ROOT / 'code/rejection_controls.json').write_text(json.dumps(negatives, indent=2) + '\n')

    rng = random.Random(20261112)
    evaluated = substituted = compiled = 0
    for _ in range(600):
        a = random_term(rng, 3, 2)
        try:
            expected = value(a, (1, 2))
            result = normal(a)
            actual = value(result, (1, 2))
        except (OverflowError, RecursionError):
            continue
        assert expected == actual
        assert normal(result) == result
        evaluated += 1
    for _ in range(600):
        h = random_term(rng, 3, 3)
        replacement = random_term(rng, 2, 1)
        try:
            result = new.sub(h, replacement, 1)
            expected = value(h, (1, value(replacement, (2,)), 2))
            actual = value(result, (1, 2))
        except (OverflowError, RecursionError):
            continue
        assert expected == actual
        substituted += 1
    for _ in range(600):
        a = random_term(rng, 3, 2, False)
        try:
            result = term(a)
            expected = value(a, (1, 2), seeded=False)
            actual = value(result, (1, 2))
            native_normal = native.walk(a, lambda i, d: i)
        except (OverflowError, RecursionError):
            continue
        assert expected == actual
        assert result == term(native_normal)
        compiled += 1

    symbolic = []
    for a in (0, S(0), -1, [3, 1, 2]):
        assert normal(P(S(a))) == normal(a)
        symbolic.append(['predecessor', a])
    for n in range(5):
        nterm = 0
        expected = -1
        for _ in range(n):
            nterm = S(nterm)
            expected = S(expected)
        assert normal(P([nterm, -1, S(S(P(1)))])) == expected
        symbolic.append(['iterator_successor', n])
    bodies = [0, 1, 2, S(1), add(2, 1), multiply(S(2), 1)]
    for index, body in enumerate(bodies):
        assert rec(0, -2, body) == -2
        expected = new.sub(new.sub(body, -1, 1), rec(-1, -2, body))
        assert rec(S(-1), -2, body) == expected
        symbolic.append(['ordinary_primitive_recursion', index])
    arithmetic = {
        'addition_3_4': (add(numeral(3), numeral(4)), 7),
        'multiplication_3_4': (multiply(numeral(3), numeral(4)), 12),
        'triangular_5': (rec(numeral(5), 0, add(S(2), 1)), 15),
        'factorial_4': (rec(numeral(4), S(0), multiply(S(2), 1)), 24),
    }
    for name, (expression, expected) in arithmetic.items():
        assert expression == numeral(expected), name

    # Exercise the standalone JSON interface with and without assertions enabled.
    cli = 0
    for optimized in (False, True):
        command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / 'code/checker.py')]
        for data, accepted in [(d, True) for d in positives.values()] + [(d, False) for d in negatives.values()]:
            result = subprocess.run(command, input=json.dumps(data), text=True, capture_output=True, timeout=10)
            assert (result.returncode == 0 and result.stdout == 'ACCEPT\n') == accepted
            cli += 1
    metrics = {str(p.relative_to(ROOT)): metric(p) for p in (ROOT / 'reference/inferred_witness/code/checker.py', ROOT / 'code/checker.py')}
    report = {'python': sys.version.split()[0], 'positive_certificates': list(positives),
              'negative_controls': list(negatives), 'cli_checks': cli,
              'independent_normalization_cases': evaluated,
              'independent_partial_substitution_cases': substituted,
              'native_compilation_cases': compiled, 'symbolic_reduction_checks': symbolic,
              'arithmetic_examples': {name: result for name, (_, result) in arithmetic.items()},
              'metrics': metrics, 'failures': 0,
              'limit': 'Finite tests only; no Lean/Rocq proof and no claim of uniform resource bounds.'}
    (ROOT / 'evidence/verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
