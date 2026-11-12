"""Independent named-variable audit of the synthesized-opening iPRA checker.

This is untrusted validation code, not part of the proof kernel.  It uses
named binders and a separate natural-number evaluator to check the kernel's
locally nameless normalization and substitution.  It also exercises the
new opening rule on genuine clause derivations and on adverse scopes.

Usage: python3 independent_validation.py /absolute/path/checker.py [result.json]
Only the Python standard library is needed.  Random tests have a fixed seed.
"""
import copy
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random
import sys


serial = itertools.count()
Z = ('z',)


def name():
    return ('bound', next(serial))


def V(x):
    return ('v', x)


def S(a):
    return ('s', a)


def I(n, a, x, h):
    return ('i', n, a, x, h)


def EQ(a, b):
    return ('eq', a, b)


def D(x, y, a):
    return ('d', x, y, a)


def term(a, scope, env=()):
    """Strict parser; independent sorted recursion, no shared kernel walker."""
    if type(a) is int:
        if a == 0:
            return Z
        if a < 0 and -scope <= a:
            return V(('free', a))
        if 1 <= a <= len(env):
            return V(env[a - 1])
        raise ValueError('term variable outside scope')
    if type(a) is not list:
        raise ValueError('term node type')
    if len(a) == 2 and type(a[0]) is int and a[0] == 0:
        return S(term(a[1], scope, env))
    if len(a) == 3:
        x = name()
        return I(term(a[0], scope, env), term(a[1], scope, env), x,
                 term(a[2], scope, (x,) + env))
    raise ValueError('term constructor')


def formula(a, scope, env=()):
    if type(a) is not list:
        raise ValueError('formula node type')
    if len(a) == 2:
        return EQ(term(a[0], scope, env), term(a[1], scope, env))
    if len(a) == 1:
        x, y = name(), name()
        return D(x, y, formula(a[0], scope, (y, x) + env))
    raise ValueError('formula constructor')


def encode(a, env=()):
    tag = a[0]
    if tag == 'z':
        return 0
    if tag == 'v':
        return a[1][1] if a[1][0] == 'free' else env.index(a[1]) + 1
    if tag == 's':
        return [0, encode(a[1], env)]
    if tag == 'i':
        _, n, b, x, h = a
        return [encode(n, env), encode(b, env), encode(h, (x,) + env)]
    if tag == 'eq':
        return [encode(a[1], env), encode(a[2], env)]
    if tag == 'd':
        _, x, y, body = a
        return [encode(body, (y, x) + env)]
    raise ValueError('named constructor')


def replace(a, x, t):
    """One simultaneous substitution on names, with explicit binding cases."""
    tag = a[0]
    if tag == 'v':
        return t if a[1] == x else a
    if tag == 'z':
        return a
    if tag == 's':
        return S(replace(a[1], x, t))
    if tag == 'i':
        _, n, b, u, h = a
        return I(replace(n, x, t), replace(b, x, t), u,
                 h if u == x else replace(h, x, t))
    if tag == 'eq':
        return EQ(replace(a[1], x, t), replace(a[2], x, t))
    if tag == 'd':
        _, u, v, body = a
        return D(u, v, body if x in (u, v) else replace(body, x, t))
    raise ValueError('named constructor')


def normal(a, fuel=None):
    if fuel is None:
        fuel = [200000]
    fuel[0] -= 1
    if fuel[0] < 0:
        raise RuntimeError('audit normalization budget exhausted')
    tag = a[0]
    if tag in ('z', 'v'):
        return a
    if tag == 's':
        return S(normal(a[1], fuel))
    if tag == 'i':
        _, n, b, u, h = a
        n, b, h = normal(n, fuel), normal(b, fuel), normal(h, fuel)
        if n == Z:
            return b
        if n[0] == 's':
            previous = normal(I(n[1], b, u, h), fuel)
            return normal(replace(h, u, previous), fuel)
        return I(n, b, u, h)
    if tag == 'eq':
        return EQ(normal(a[1], fuel), normal(a[2], fuel))
    if tag == 'd':
        return D(a[1], a[2], normal(a[3], fuel))
    raise ValueError('named constructor')


def value(a, assignment, fuel=None):
    """Numerical meaning uses a Python loop, no rewriting or substitution."""
    if fuel is None:
        fuel = [200000]
    fuel[0] -= 1
    if fuel[0] < 0:
        raise RuntimeError('audit evaluation budget exhausted')
    tag = a[0]
    if tag == 'z':
        return 0
    if tag == 'v':
        return assignment[a[1]]
    if tag == 's':
        return 1 + value(a[1], assignment, fuel)
    if tag == 'i':
        _, n, b, u, h = a
        count = value(n, assignment, fuel)
        result = value(b, assignment, fuel)
        for _ in range(count):
            result = value(h, assignment | {u: result}, fuel)
        return result
    raise ValueError('evaluator requires a term')


rng = random.Random(20261111)


def random_term(depth, scope, env=()):
    atoms = [Z] + [V(('free', -i)) for i in range(1, scope + 1)] + [V(x) for x in env]
    if depth == 0 or rng.randrange(4) == 0:
        return rng.choice(atoms)
    if rng.randrange(2) == 0:
        return S(random_term(depth - 1, scope, env))
    u = name()
    counter = rng.choice(atoms + [S(Z), S(S(Z))])
    return I(counter, random_term(depth - 1, scope, env), u,
             random_term(depth - 1, scope, (u,) + env))


def random_formula(depth, scope, env=()):
    if depth and rng.randrange(3) == 0:
        x, y = name(), name()
        return D(x, y, random_formula(depth - 1, scope, (y, x) + env))
    return EQ(random_term(3, scope, env), random_term(3, scope, env))


def selector(v, a, b):
    return I(v, a, name(), b)


def packet(x, y, zero_left, zero_right, unit_left, unit_right, two_left, two_right):
    p = name()
    parity = I(V(y), Z, p, selector(V(p), S(Z), Z))
    left = selector(V(y), zero_left, selector(parity, two_left, unit_left))
    right = selector(V(y), zero_right, selector(parity, two_right, unit_right))
    return normal(EQ(left, right))


def load(path):
    spec = importlib.util.spec_from_file_location('audited_checker', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def succeeds(action):
    try:
        return True, action()
    except Exception as exc:
        return False, type(exc).__name__


def run(path):
    k = load(path)
    checks = {}
    failures = []

    def expect(label, condition, detail=None):
        checks[label] = checks.get(label, 0) + 1
        if not condition:
            failures.append({'category': label, 'detail': detail})
            if len(failures) > 10:
                raise RuntimeError('multiple independent validation failures')

    # Named normal forms, numerical meanings, and canonical-syntax recognition.
    for i in range(700):
        scope = i % 4
        is_formula = i % 3 == 0
        a = random_formula(2, scope) if is_formula else random_term(3, scope)
        raw = encode(a)
        expected = encode(normal(a))
        actual = k.walk(raw, lambda j, d: j, form=is_formula)
        expect('named_normalization', actual == expected, {'input': raw, 'expected': expected, 'actual': actual})
        ok, _ = succeeds(lambda: k.syntax(raw, scope + 1, is_formula))
        expect('canonical_syntax', ok == (raw == expected), raw)
        if not is_formula:
            for shift in range(3):
                assignment = {('free', -j): (shift + j) % 3 for j in range(1, scope + 1)}
                expect('numerical_semantics', value(a, assignment) == value(normal(a), assignment), raw)

    # Opening protected binders and older bound variables catches index shifts.
    for i in range(500):
        protected = tuple(name() for _ in range(i % 3))
        target = name()
        older = tuple(name() for _ in range((i // 3) % 3))
        scope = (i // 9) % 3
        is_formula = i % 2 == 0
        env = protected + (target,) + older
        a = random_formula(1, scope, env) if is_formula else random_term(3, scope, env)
        t = normal(random_term(2, scope, older))
        raw = encode(normal(a), env)
        actual = k.sub(raw, encode(t, older), len(protected))
        expected = encode(normal(replace(normal(a), target, t)), protected + older)
        expect('capture_avoiding_opening', actual == expected,
               {'input': raw, 'target': encode(t, older), 'depth': len(protected), 'actual': actual, 'expected': expected})

    # Free-name replacement can deliberately contain that same free name.
    for i in range(400):
        scope = 1 + i % 3
        a = normal(random_formula(2, scope))
        target = ('free', -1)
        t = normal(random_term(3, scope))
        expected = encode(normal(replace(a, target, t)))
        actual = k.walk(encode(a), lambda j, d: encode(t) if j == -1 else j)
        expect('simultaneous_free_substitution', actual == expected, {'formula': encode(a), 'term': encode(t)})

    # Independent named guard and specialized-clause comparison.
    selected_count = 0
    for i in range(350):
        x, y = name(), name()
        scope = i % 3
        if i % 2:
            matrix = normal(random_formula(1, scope, (y, x)))
        else:
            right = random_term(2, scope, (x,))
            matrix = packet(x, y, Z, Z, V(x), right,
                            random_term(2, scope, (x,)), random_term(2, scope, (x,)))
        b = ('free', -scope - 1)
        opened = normal(replace(matrix, x, V(b)))
        base = normal(replace(opened, y, Z))
        unit = normal(replace(opened, y, S(Z)))
        replacement = unit[2] if base == EQ(Z, Z) and unit[0] == 'eq' and unit[1] == V(b) else V(b)
        selected_count += replacement != V(b)
        raw_matrix = encode(matrix, (y, x))
        raw_body = k.sub(raw_matrix, b[1], 1)
        raw_base, raw_unit = k.sub(raw_body, 0), k.sub(raw_body, [0, 0])
        raw_t = raw_unit[1] if raw_base == [0, 0] and raw_unit[0] == b[1] else b[1]
        expect('guard_selection', raw_t == encode(replacement), raw_matrix)
        specialized = normal(replace(opened, b, replacement))
        actual = k.walk(raw_body, lambda j, d: raw_t if j == b[1] else j)
        expect('specialized_open_clause', actual == encode(specialized, (y,)), raw_matrix)
        # The implementation retains the original base.  This is valid:
        # selection proves base=H; fallback substitutes the identity.
        new_base = normal(replace(specialized, y, Z))
        expect('retained_base_invariant', encode(new_base) == raw_base, raw_matrix)

    # Concrete clause proofs test the real E implementation, including scopes.
    refl_context = [([], [1, 1])]
    zero, one, two = 0, [0, 0], [0, [0, 0]]
    hproof = ['u', 0, zero, None]

    def run_open(matrix, branch, outer_count=2):
        # One arbitrary closed paired assumption, a legitimate contextual test.
        g = refl_context + [([], [matrix])]
        proof = ['e', ['u', 1, 0, None], branch]
        return succeeds(lambda: k.prove(proof, g))

    cases = []
    for kind in ('selected_closed', 'selected_identity', 'self_erased', 'self_escapes',
                 'nonzero_reflexive_base', 'nonreflexive_base', 'reverse_unit', 'compound'):
        x, y = name(), name()
        base_l = base_r = Z
        unit_l, unit_r = V(x), Z
        row_l, row_r = V(x), V(x)
        expected_ok, expected_value = True, [0, 0]
        if kind == 'selected_identity':
            unit_r = V(x)
            row_l = row_r = Z
        elif kind in ('self_erased', 'self_escapes'):
            unit_r = S(V(x))
            if kind == 'self_erased':
                row_l, row_r = I(V(x), Z, name(), Z), Z
            else:
                row_l, row_r = V(x), S(V(x))
                expected_ok = False
        elif kind == 'nonzero_reflexive_base':
            base_l = base_r = S(Z)
            expected_ok = False
        elif kind == 'nonreflexive_base':
            base_l, base_r = Z, S(Z)
            expected_ok = False
        elif kind == 'reverse_unit':
            unit_l, unit_r = Z, V(x)
            expected_ok = False
        elif kind == 'compound':
            u, v = name(), name()
            matrix = encode(D(u, v, EQ(Z, Z)), (y, x))
            outcome = run_open(matrix, hproof)
            expect('opening_rule_edges', outcome == (True, [0, 0]), {'case': kind, 'outcome': outcome})
            cases.append({'case': kind, 'accepted': outcome[0]})
            continue
        matrix = encode(packet(x, y, base_l, base_r, unit_l, unit_r, row_l, row_r), (y, x))
        if kind in ('nonzero_reflexive_base', 'nonreflexive_base', 'reverse_unit'):
            # If the guard were wrongly selected, this would become a closed
            # reflexivity.  Correct fallback leaves the fresh name and rejects.
            branch = ['u', 0, -2, None]
        else:
            branch = ['u', 2, two, hproof]
        outcome = run_open(matrix, branch)
        expect('opening_rule_edges', outcome[0] == expected_ok and (not expected_ok or outcome[1] == expected_value),
               {'case': kind, 'outcome': outcome})
        cases.append({'case': kind, 'accepted': outcome[0]})

    # Closed proofs and malformed public inputs, including Python equality aliases.
    major = ['i', [0, 0], one, hproof]
    examples = [
        {'goal': [0, 0], 'proof': hproof},
        {'goal': [[0, 0]], 'proof': major},
        {'goal': [0, 0], 'proof': ['e', major, hproof]},
    ]
    for cert in examples:
        ok, _ = succeeds(lambda: k.check(cert))
        expect('closed_positive_certificates', ok, cert)
    negatives = [
        {'goal': [False, False], 'proof': hproof},
        {'goal': [0.0, 0.0], 'proof': hproof},
        {'goal': [-1, -1], 'proof': ['u', 0, -1, None]},
        {'goal': [1, 1], 'proof': ['u', 0, 1, None]},
        {'goal': [0, one], 'proof': hproof},
        {'goal': [0, 0], 'proof': ['u', True, 0, None]},
        {'goal': [0, 0], 'proof': ['u', -1, 0, None]},
        {'goal': [0, 0], 'proof': ['u', 1, 0, None]},
        {'goal': [0, 0], 'proof': ['e', hproof, hproof]},
        {'goal': [0, 0], 'proof': ['i', [0, 0], False, hproof]},
        {'goal': [[False, False]], 'proof': ['i', [False, False], one, hproof]},
        {'goal': [0, 0], 'proof': ['e', major, ['u', 0, -1, None]]},
        {'goal': [[0, 0]], 'proof': ['i', [0, 0], one, ['u', 0, one, None]]},
        {'goal': [0, 0], 'proof': hproof, 'extra': 0},
        ['goal', 'proof'],
        None,
    ]
    for cert in negatives:
        ok, error = succeeds(lambda: k.check(cert))
        expect('adversarial_public_certificates', not ok, {'certificate': cert, 'result': error})

    # Structurally malformed input must be rejected even under an erased body.
    bad_terms = [True, False, 0.0, '0', None, {}, [], [0], [1, 0],
                 [0, True], [0, 0, True], [0, 0, []], [0, 0, [1, 0]],
                 [0, 0, 2], [0, 0, 0, 0], -1, 1]
    for raw in bad_terms:
        ok, _ = succeeds(lambda: k.syntax(raw, 1, False))
        expect('malformed_erased_syntax', not ok, raw)

    # An independent parser decides acceptance of arbitrary small JSON trees.
    # This includes malformed nodes hidden in branches erased by computation.
    atoms = [None, False, True, -3, -2, -1, 0, 1, 2, 3, 0.0, 1.0, 'd', {}, '']

    def raw_tree(depth):
        if depth == 0 or rng.randrange(3) == 0:
            return copy.deepcopy(rng.choice(atoms))
        return [raw_tree(depth - 1) for _ in range(rng.randrange(5))]

    for i in range(1500):
        scope, is_formula = i % 4, i % 2 == 0
        if i % 5:
            raw = raw_tree(3)
        else:
            a = normal(random_formula(2, scope) if is_formula else random_term(3, scope))
            raw = encode(a)
            if i % 10 and type(raw) is list:
                raw[rng.randrange(len(raw))] = raw_tree(2)
        def independent_accepts():
            parsed = (formula if is_formula else term)(raw, scope)
            return encode(normal(parsed)) == raw
        parse_ok, canonical = succeeds(independent_accepts)
        expected = parse_ok and canonical
        actual, _ = succeeds(lambda: k.syntax(raw, scope + 1, is_formula))
        expect('independent_grammar_fuzz', actual == expected,
               {'input': raw, 'scope': scope, 'form': is_formula, 'expected': expected, 'actual': actual})

    result = {
        'checker': str(Path(path).resolve()),
        'checker_sha256': hashlib.sha256(Path(path).read_bytes()).hexdigest(),
        'python': sys.version.split()[0],
        'seed': 20261111,
        'method': 'independent named binders, structural parser, natural-number loop evaluator, direct clause derivations',
        'checks': checks,
        'total_checks': sum(checks.values()),
        'selected_random_guards': selected_count,
        'opening_edge_cases': cases,
        'failures': failures,
        'limits': 'Finite implementation evidence; no formal proof or consistency inference. Internal-context cases assume their stated major formula.',
    }
    return result


if __name__ == '__main__':
    result = run(sys.argv[1])
    text = json.dumps(result, indent=2) + '\n'
    if len(sys.argv) > 2:
        Path(sys.argv[2]).write_text(text)
    print(text)
    if result['failures']:
        raise SystemExit(1)
