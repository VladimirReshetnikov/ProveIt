"""Verify the raw parameter calculus, translations, and its public interface."""
import ast
import copy
import gzip
import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tokenize

import raw_parameter as new
import raw_template_control as old
from translate_raw import backward, forward, refl, translate

ROOT = Path(__file__).resolve().parent


def require(condition, detail):
    if not condition:
        raise RuntimeError(detail)


def accepts(checker, data):
    try:
        checker.verify(data)
        return True
    except Exception:
        return False


def numeral(n):
    t = 0
    for _ in range(n):
        t = [0, t]
    return t


def old_refl(a):
    p = ['c', 0, a, 1]
    return ['x', 1, p, p]


def old_sym(p, context=(), scope=0):
    a, b = old.derive(p, list(context), scope)
    return ['x', 1, old_refl(a), p]


def old_zero(a, h):
    return ['c', 0, a, h]


def old_succ(n, a, h):
    return ['c', [0, n], a, h]


def build_extra_controls():
    out = {}
    major = old_zero(0, 1)
    s = [0, 0, 1]
    templates = {
        'passive_source_occurrences': [s, 1, s],
        'nested_bound_passive_occurrences': [1, s, [2, 1, [3, 2, 1]]],
        'counter_and_initializer_occurrences': [1, 1, 2],
        'successor_payload': [0, 1],
    }
    for name, template in templates.items():
        minor = old_refl(old.opening(template, s))
        out[name] = ['x', template, major, minor]
    zero_major = old_sym(major)
    for name, template in {'zero_source_successor_tag': [0, 1],
                           'zero_source_passive_zeros': [1, 0, [0, 2]]}.items():
        out[name] = ['x', template, zero_major,
                     old_refl(old.opening(template, 0))]
    return out


def test_translations():
    controls = {p.stem: json.loads(p.read_text())
                for p in sorted((ROOT / 'raw_examples/control').glob('*.json'))}
    for name, proof in build_extra_controls().items():
        controls[name] = {'goal': old.derive(proof, [], 0), 'proof': proof}
    out = ROOT / 'raw_examples/parameter'
    out.mkdir(parents=True, exist_ok=True)
    targets = {}
    for name, source in controls.items():
        old.verify(source)
        target = translate(source)
        back = translate(target, False)
        require(back['goal'] == source['goal'], ('round-trip goal', name))
        targets[name] = target
        (out / (name + '.json')).write_text(json.dumps(target, indent=2) + '\n')
    return controls, targets


def reference_open(a, value, index, depth=0):
    """Separate positive-binder and negative-free-parameter definitions."""
    if type(a) is int:
        if index < 0:
            return value if a == index else a
        at = index + depth
        return value if a == at else a - (a > at)
    result = []
    for i, child in enumerate(a):
        if len(a) == 1:
            child_depth = depth + 2
        elif len(a) == 3 and i == 2:
            child_depth = depth + 1
        else:
            child_depth = depth
        result.append(reference_open(child, value, index, child_depth))
    return result


def evaluate(term, environment, free, budget):
    budget[0] -= 1
    if budget[0] < 0:
        raise OverflowError('evaluation budget')
    if type(term) is int:
        return environment[term - 1] if term > 0 else free[term] if term < 0 else 0
    if len(term) == 2:
        return 1 + evaluate(term[1], environment, free, budget)
    n, a, h = term
    n = evaluate(n, environment, free, budget)
    if n > 64:
        raise OverflowError('large iterator counter')
    value = evaluate(a, environment, free, budget)
    for _ in range(n):
        value = evaluate(h, [value] + environment, free, budget)
    return value


def test_opening():
    rng = random.Random(20261111)

    def term(size, depth):
        atoms = list(range(-3, depth + 1))
        if size == 0 or rng.randrange(3) == 0:
            return rng.choice(atoms)
        if rng.randrange(2):
            return [0, term(size - 1, depth)]
        return [rng.choice(atoms + [numeral(1), numeral(2)]),
                term(size - 1, depth), term(size - 1, depth + 1)]

    syntactic = semantic = skipped = 0
    for _ in range(800):
        index = rng.choice([-3, -2, -1, 1, 2])
        depth = max(index, 0)
        value = term(2, 0)
        body = term(2, depth)
        expected = reference_open(body, value, index)
        actual = new.opening(body, value, index)
        require(actual == expected, ('opening mismatch', body, value, index))
        require(new.valid(actual, 3, max(depth - (index > 0), 0)),
                ('opening result scope', body, value, index))
        syntactic += 2
        formula = [[body, body]]
        require(new.opening(formula, value, index) == reference_open(formula, value, index),
                'nested formula opening mismatch')
        syntactic += 1
        free = {-1: rng.randrange(3), -2: rng.randrange(3), -3: rng.randrange(3)}
        environment = [rng.randrange(3) for _ in range(depth)]
        try:
            v = evaluate(value, [], free, [20000])
            if index < 0:
                lhs = evaluate(actual, [], free, [20000])
                rhs = evaluate(body, [], dict(free, **{} ) | {index: v}, [20000])
            else:
                remaining = environment[:index - 1] + environment[index:]
                inserted = environment[:index - 1] + [v] + environment[index:]
                lhs = evaluate(actual, remaining, free, [20000])
                rhs = evaluate(body, inserted, free, [20000])
            require(lhs == rhs, ('semantic substitution mismatch', body, value, index))
            semantic += 1
        except OverflowError:
            skipped += 1
    # Negative replacement is simultaneous: an occurrence in the inserted
    # value is never revisited. Bound indices are not free parameter labels.
    require(new.opening([-1, 0, [1, -1, 2]], [0, -1], -1)
            == [[0, -1], 0, [1, [0, -1], 2]], 'negative replacement capture')
    require(new.opening([2, 1, 3], 0, 2) == [0, 1, 0],
            'second bound coordinate opening')
    return syntactic + 2, semantic, skipped


def test_parameter_boundary():
    checks = 0
    # All these checks are open sequents under explicit retained equations.
    # They do not assert that false premises are closed theorems.
    cases = [
        (0, numeral(1), numeral(1), numeral(1)),
        ([0, 0, 1], 0, [[0, 0, 1], 0, 1], [[0, 0, 1], 0, 1]),
        (-1, numeral(1), [-1, 0, [1, -1, 2]],
         [numeral(1), 0, [1, numeral(1), 2]]),
        (-1, [0, -1], [-1, -1, 1], [[0, -1], [0, -1], 1]),
    ]
    for s, t, u, replaced in cases:
        scope = 1 if any(v == -1 for v in (s,)) else 0
        context = [([0, 0], [s, t])]
        major = ['u', 0, 0, refl(0)]
        proof = ['x', major, refl(u)]
        require(new.derive(proof, context, scope) == [u, replaced],
                ('wrong proper replacement', s, t, u))
        translated = backward(proof, context, scope)
        require(old.derive(translated, context, scope) == [u, replaced],
                'boundary reverse translation')
        checks += 2
    # Root composition is unrestricted even when the common source is 0
    # or an iterator. It never traverses a target inserted at the root.
    for s in (0, numeral(1), [0, 0, 1], -1):
        scope = int(s == -1)
        context = [([0, 0], [s, 0])]
        p = ['u', 0, 0, refl(0)]
        require(new.derive(['x', p, refl(s)], context, scope) == [s, 0],
                'unrestricted root composition failed')
        checks += 1
    return checks


def rejection_cases(targets):
    r0 = refl(0)
    base = {'goal': [0, 0], 'proof': r0}
    result = {
        'extra_field': dict(base, extra=0),
        'boolean_seed': {'goal': [False, False], 'proof': ['c', 0, False, 1]},
        'boolean_successor': {'goal': [0, 0], 'proof': ['c', [False, 0], 0, 1]},
        'float_seed': {'goal': [0, 0], 'proof': ['c', 0, 0.0, 1]},
        'free_seed': {'goal': [0, 0], 'proof': ['c', 0, -1, 1]},
        'loose_bound_seed': {'goal': [0, 0], 'proof': ['c', 0, 1, 1]},
        'loose_bound_body': {'goal': [0, 0], 'proof': ['c', 0, 0, 2]},
        'unknown_rule': {'goal': [0, 0], 'proof': ['r', 0]},
        'extra_rule_argument': {'goal': [0, 0], 'proof': ['c', 0, 0, 1, 0]},
        'forged_goal': {'goal': [0, numeral(1)], 'proof': r0},
        'nonexistent_clause': {'goal': [0, 0], 'proof': ['u', 0, 0, r0]},
        'boolean_clause_index': {'goal': [0, 0], 'proof': ['u', False, 0, r0]},
        'negative_clause_index': {'goal': [0, 0], 'proof': ['u', -1, 0, r0]},
        'iterator_counter_not_successor': {'goal': [0, 0], 'proof': ['c', [0, 0, 1], 0, 1]},
        'witness_escape': {'goal': [[0, 0]], 'proof': ['i', [[0, 0]], -1, r0]},
        'empty_proof': {'goal': [0, 0], 'proof': []},
        'string_proof': {'goal': [0, 0], 'proof': 'c000'},
        'object_proof': {'goal': [0, 0], 'proof': {'c': 0, '0': 0, '1': 0, '2': 0}},
        'null_root': None,
        'array_root': ['goal', 'proof'],
    }
    paired = targets['used_induction_hypothesis']['proof']
    result['equation_rule_with_D_major'] = {'goal': [0, 0], 'proof': ['x', paired, r0]}
    result['elimination_escape'] = {'goal': [0, 0], 'proof': ['e', [0, 0], paired, refl(-1)]}
    result['elimination_out_of_scope'] = {'goal': [0, 0], 'proof': ['e', [0, 0], paired, refl(-2)]}
    result['variable_counter_not_successor'] = {
        'goal': [[0, 0]], 'proof': ['i', [[0, 0]], 0, ['c', -1, 0, 1]]}
    bad_mode = copy.deepcopy(targets['used_induction_hypothesis'])
    bad_mode['proof'][2] = numeral(1)
    result['retagged_induction_as_cases'] = bad_mode
    # A direct parameter-equality instruction may not silently do general
    # congruence at a zero source; the fresh-alias derivation is necessary.
    p = ['c', 0, 0, 1]
    s = [0, 0, 1]
    zero_s = ['x', refl(s), p]
    result['forbidden_proper_zero_replacement'] = {
        'goal': [numeral(1), [0, s]], 'proof': ['x', zero_s, refl(numeral(1))]}
    for name, data in result.items():
        require(not accepts(new, data), ('accepted adversarial certificate', name))
    return result


def measure(name):
    p = ROOT / (name + '.py')
    tree = ast.parse(p.read_text())
    if isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant):
        tree.body.pop(0)
    source = ast.unparse(tree) + '\n'
    tokens = sum(t.type not in {tokenize.ENCODING, tokenize.ENDMARKER,
                 tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT,
                 tokenize.COMMENT} for t in tokenize.generate_tokens(io.StringIO(source).readline))
    return {'program': name, 'normalized_bytes': len(source.encode()),
            'tokens': tokens, 'ast_nodes': len(list(ast.walk(tree))),
            'gzip9_bytes': len(gzip.compress(source.encode(), mtime=0))}


def main():
    controls, targets = test_translations()
    syntactic, semantic, skipped = test_opening()
    boundary = test_parameter_boundary()
    rejected = rejection_cases(targets)
    cli_runs = 0
    for optimized in (False, True):
        for expected, examples in ((True, targets), (False, rejected)):
            for name, data in examples.items():
                args = [sys.executable] + (['-O'] if optimized else [])
                args += [str(ROOT / 'raw_parameter.py')]
                run = subprocess.run(args, input=json.dumps(data), text=True,
                                     capture_output=True, check=False)
                require((run.returncode == 0) == expected, ('CLI status', name))
                require(run.stdout.strip() == ('ACCEPT' if expected else 'REJECT'),
                        ('CLI output', name))
                cli_runs += 1
    (ROOT / 'raw_examples/reject_forbidden_proper_zero.json').write_text(
        json.dumps(rejected['forbidden_proper_zero_replacement'], indent=2) + '\n')
    result = {'python': sys.version, 'positive_examples': len(targets),
              'negative_examples': len(rejected), 'translation_runs': 2 * len(targets),
              'syntactic_opening_checks': syntactic, 'semantic_opening_checks': semantic,
              'semantic_cases_skipped_for_budget': skipped,
              'parameter_boundary_checks': boundary, 'public_cli_runs': cli_runs,
              'metrics': [measure(n) for n in ('raw_parameter', 'raw_template_control',
                          'raw_shared_opener_control', 'raw_ce5_control')],
              'limits': 'Finite executable validation; no new proof-assistant verification.'}
    (ROOT / 'raw_verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
