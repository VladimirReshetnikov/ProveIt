"""Finite validation, independent numerical semantics, and exact size report.

This file is not imported by either acceptance checker.
"""
import ast
import copy
import gzip
import importlib.util
import io
import json
import pathlib
import random
import subprocess
import sys
import tokenize

import counter_name3_matched as kernel
import counter_name3_fuel as fuel_kernel
import proof_tools as p

HERE = pathlib.Path(__file__).resolve().parent


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def accepted(document, checker=kernel):
    try:
        checker.check(copy.deepcopy(document))
        return True
    except Exception:
        return False


def metrics(path):
    tree = ast.parse(path.read_text())
    if (tree.body and isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and isinstance(tree.body[0].value.value, str)):
        tree.body.pop(0)
    data = (ast.unparse(tree) + '\n').encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {'bytes': len(data),
            'tokens': sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(data.decode()).readline)),
            'AST': sum(1 for _ in ast.walk(tree)),
            'gzip9': len(gzip.compress(data, compresslevel=9, mtime=0))}


def evaluate(term, bound=(), free=None):
    """Independent direct mathematical evaluator; no substitution or normalization."""
    free = free or {}
    if type(term) is int:
        return 0 if term == 0 else bound[term - 1] if term > 0 else free[term]
    n, a, h = term
    count = evaluate(n, bound, free)
    value = evaluate(a, bound, free) + 1
    if count > 100:
        raise OverflowError('independent evaluator resource cap')
    for counter in range(count):
        value = evaluate(h, (value, counter) + bound, free)
    if value > 1000000:
        raise OverflowError('independent evaluator resource cap')
    return value


def goal_directed(a, proof, context=p.INITIAL):
    """Independent rule dispatch with explicit body, conclusion, and target fields.

This replay shares the term normalizer; independent numerical evaluation is
tested separately below. It does not call kernel.prove.
"""
    n = len(context)
    kernel.syntax(a, n, True)
    match proof:
        case ['u', j, t, premise]:
            if type(j) is not int or not 0 <= j < n:
                raise ValueError('index')
            kernel.syntax(t, n)
            base, body = context[j]
            if a != kernel.sub(body, t):
                raise ValueError('use')
            if base:
                goal_directed(base, premise, context)
        case ['i', t, branch]:
            if len(a) != 1:
                raise ValueError('intro')
            kernel.syntax(t, n)
            body = kernel.sub(a[0], t, 1)
            base = kernel.sub(body, -n if len(a[0]) == 2 and t == 0 else 0)
            goal_directed(kernel.sub(body, p.S(-n)), branch, context + [([], base)])
        case ['e', body, formula, target, major, equality, branch]:
            goal_directed([body], major, context)
            B = kernel.sub(body, -n, 1)
            local = context + [(kernel.sub(B, 0), B)]
            goal_directed([-n, target], equality, local)
            goal_directed(formula, branch, local)
            if p.at(formula, -n, target) != a:
                raise ValueError('export')
        case _:
            raise ValueError('proof')


def translate_uniform(a, q, old, context=(), new_context=p.INITIAL):
    """Replay old zero-normal counter-R fixtures in full-normal Name3.

The one guard-changing witness case is deliberately reported as unsupported;
this is a fixture translator, not a claimed general proof transformation.
"""
    if len(a) == 2 and a[0] == a[1]:
        return p.refl(p.normal(a[0]))
    match q:
        case ['v', s, t, b, h, major, minor]:
            eq = translate_uniform([s, t], major, old, context, new_context)
            before = [[[0, s, 0], b, h], a[0]]
            mn = translate_uniform(before, minor, old, context, new_context)
            template = kernel.sub(kernel.sub(h, p.X, 1), p.normal([p.X, b, h]))
            return p.crossed_transport(eq, mn, template, p.X, new_context)
        case ['u', j, t, premise]:
            premise2 = (translate_uniform(context[j][0], premise, old, context, new_context)
                        if new_context[j + 1][0] else None)
            return p.use(j + 1, p.normal(t), premise2)
        case ['e', body, major, branch]:
            maj = translate_uniform([body], major, old, context, new_context)
            fresh = -len(context) - 1
            B = old.opening(body, fresh, 1)
            BN = kernel.sub(p.normal(body), fresh, 1)
            local = tuple(context) + ((old.opening(B, 0), B),)
            localN = new_context + [(kernel.sub(BN, 0), BN)]
            br = translate_uniform(a, branch, old, local, localN)
            return ['e', maj, p.refl(fresh), br]
        case ['i', t, branch]:
            fresh = -len(context) - 1
            body = old.opening(a[0], t, 1)
            base = old.opening(body, fresh if len(a[0]) == 2 and t == 0 else 0)
            step = old.opening(body, p.S(fresh))
            tN, BN = p.normal(t), p.normal(a[0])
            if len(a[0]) == 2 and (t == 0) != (tN == 0):
                raise NotImplementedError('witness becomes literal zero')
            bodyN = kernel.sub(BN, tN, 1)
            baseN = kernel.sub(bodyN, fresh if len(BN) == 2 and tN == 0 else 0)
            br = translate_uniform(step, branch, old,
                                   tuple(context) + (([0, 0], base),),
                                   new_context + [([], baseN)])
            return ['i', BN, tN, br]
    raise ValueError('old proof')


def main():
    examples = {}
    examples['reflexivity'] = p.refl(p.TWO)
    examples['symmetry'] = p.implication([0, p.ONE], [p.ONE, 0],
                                         lambda h, g: p.symmetry(h, g))
    examples['successor_congruence'] = p.implication([0, p.ONE], [p.ONE, p.TWO],
        lambda h, g: p.transport(p.symmetry(h, g), p.refl(p.TWO), p.S(p.V), p.V, g))
    def transitivity_builder(h, g):
        reverse = p.symmetry(h, g)
        successor = p.transport(reverse, p.refl(p.TWO), p.S(p.V), p.V, g)
        return p.transport(reverse, successor, p.V, p.V, g)
    examples['transitivity'] = p.implication([0, p.ONE], [0, p.TWO], transitivity_builder)
    examples['nested_congruence'] = p.implication([0, p.ONE], [p.S(p.ONE), p.S(p.TWO)],
        lambda h, g: p.transport(p.symmetry(h, g), p.refl(p.S(p.TWO)), p.S(p.S(p.V)), p.V, g))
    # The target still contains the fresh witness. From b=S(b) export
    # F[S(b)/b] with F independent of b, so outer scope is still respected.
    def self_target_builder(h, g):
        packet = p.D([p.C(p.Y, 0, p.X), p.C(p.Y, 0, p.S(p.X))])
        fresh = -len(g)
        major = ['i', packet[0], 0, p.weaken(h, len(g))]
        equality = p.use(len(g), p.ONE, p.refl(0))
        return ['e', major, equality, p.refl(p.TWO)]
    examples['self_containing_target'] = p.implication([0, p.ONE], [p.TWO, p.TWO], self_target_builder)
    alias_packet = p.D([p.C(p.Y, 0, p.X), 0])
    alias_major = ['i', alias_packet[0], 0, p.refl(0)]
    nested_branch = ['i', [-1, -1], 0, p.refl(-1)]
    examples['nested_formula_export'] = ['e', alias_major, p.use(1, p.ONE, p.refl(0)), nested_branch]
    changed = json.loads((HERE / 'control_examples/witness_case_computable_zero.json').read_text())
    examples['guard_changed_zero_witness_repaired'] = ['i', p.normal(changed['goal'][0]), 0, p.refl(0)]
    oldpath = HERE / 'control_uniform.py'
    translated, skipped = [], []
    if oldpath.exists():
        old = load(oldpath, 'uniform_old')
        for file in sorted((HERE / 'control_examples').glob('*.json')):
            c = json.loads(file.read_text())
            old.check(c)
            try:
                proof = translate_uniform(c['goal'], c['proof'], old)
            except NotImplementedError as error:
                skipped.append({'file': file.name, 'reason': str(error)})
                continue
            goal = p.normal(c['goal'])
            if kernel.prove(proof, p.INITIAL) != goal:
                raise AssertionError(file.name)
            examples['translated_' + file.stem] = proof
            translated.append(file.name)
    out = HERE / 'examples'
    out.mkdir(exist_ok=True)
    accepted_docs = []
    fuel_costs = {}
    replays = 0
    for name, proof in examples.items():
        goal = kernel.prove(proof, p.INITIAL)
        document = {'goal': goal, 'proof': proof}
        assert accepted(document), name
        goal_directed(goal, p.to_old(goal, proof))
        replays += 1
        (out / (name + '.json')).write_text(json.dumps(document, separators=(',', ':')) + '\n')
        budget = 10000000
        fuel_doc = dict(document, fuel=budget)
        assert accepted(fuel_doc, fuel_kernel), name
        used = budget - fuel_kernel.fuel
        assert accepted(dict(document, fuel=used), fuel_kernel), name
        assert not accepted(dict(document, fuel=used - 1), fuel_kernel), name
        fuel_costs[name] = used
        accepted_docs.append(document)
    invalid = []
    r = {'goal': [0, 0], 'proof': p.refl(0)}
    for value in [True, False, 0.0, '0', None, {}, [], 1, -1]:
        invalid.append({'goal': [value, value], 'proof': ['u', 0, value, None]})
    invalid += [dict(r, extra=0), {'goal': [0, 0]}, [], {},
                {'goal': [0, p.ONE], 'proof': p.refl(0)},
                {'goal': [0, 0], 'proof': ['bogus']},
                {'goal': [0, 0], 'proof': ['u', True, 0, None]},
                {'goal': [0, 0], 'proof': ['u', -1, 0, None]},
                {'goal': [0, 0], 'proof': ['u', 999, 0, None]},
                {'goal': [0, 0], 'proof': ['u', 0, 0, None, 0]},
                {'goal': [[0, 0, 1], [0, 0, 1]], 'proof': p.refl(0)},
                {'goal': [[0, 0, True], [0, 0, True]], 'proof': p.refl(0)},
                {'goal': [[0, 0, 3], [0, 0, 3]], 'proof': p.refl(0)}]
    trivial_major = ['i', [0, 0], 0, p.refl(0)]
    invalid += [
        {'goal': [0, 0], 'proof': ['e', trivial_major, p.refl(0), p.refl(0)]},
        {'goal': [-1, -1], 'proof': ['e', trivial_major, p.refl(-1), p.refl(-1)]},
        {'goal': [0, 0], 'proof': ['e', p.refl(0), p.refl(-1), p.refl(0)]},
    ]
    for c in invalid:
        assert not accepted(c), c
    malformed_fuel = 0
    for value in [True, False, -1, 0.0, '100', None, [], {}]:
        assert not accepted(dict(r, fuel=value), fuel_kernel)
        malformed_fuel += 1
    # Binder capture regression: an inner successor recursion carries an
    # ambient bound variable in its predecessor value. The old state-first
    # expansion wrongly captures it as the recursion counter.
    regressions = [
        [[0, 0, 0], 1, 1],
        [[0, 0, 0], 1, 3],
        [[0, [0, 0, 0], 0], 1, [0, 1, 0]],
        [[0, 1, 0], 2, 1],
        [1, 0, [[0, 0, 0], 3, 1]],
        [1, 0, [[0, 0, 0], 3, 3]],
    ]
    semantic_checks = 0
    for term in regressions:
        nf = p.normal(term)
        for a in range(4):
            for b in range(4):
                assert evaluate(term, (a, b, 2)) == evaluate(nf, (a, b, 2)), (term, nf)
                semantic_checks += 1
    bad = regressions[0]
    c, seed, h = bad
    previous = p.normal([c[1], seed, h])
    wrong = kernel.sub(kernel.sub(h, previous), c[1])
    assert evaluate(bad, (2, 3)) != evaluate(wrong, (2, 3))
    # Two distinct free numerical parameters, no closed-goal convenience.
    open_context = p.INITIAL + [([], [-1, -2]), ([], [0, 0])]
    open_proof = p.transport(p.use(1, 0), p.refl(p.S(-1)), p.S(p.V), p.V, open_context)
    assert kernel.prove(open_proof, open_context) == [p.S(-2), p.S(-1)]
    rng = random.Random(20261111)
    def term(depth, budget):
        if budget <= 0 or rng.randrange(3) == 0:
            return rng.randrange(depth + 1)
        count = rng.randrange(3)
        counter = 0
        for _ in range(count):
            counter = p.S(counter)
        return [counter, term(depth, budget - 1), term(depth + 2, budget - 1)]
    generated = 0
    for _ in range(250):
        t = term(2, 3)
        nf = p.normal(t)
        assert p.normal(nf) == nf
        for values in [(0, 0), (1, 2), (3, 1)]:
            assert evaluate(t, values) == evaluate(nf, values), (t, nf, values)
            semantic_checks += 1
        generated += 1
    identities = 0
    for n in range(5):
        num = 0
        for _ in range(n):
            num = p.S(num)
        for a in range(4):
            anum = 0
            for _ in range(a):
                anum = p.S(anum)
            assert evaluate(p.C(num, anum, p.TWO)) == (a if n == 0 else 2)
            add = p.J(num, anum, p.W, p.U, p.S(p.U))
            assert evaluate(add) == n + a
            counter_state = p.J(num, anum, p.W, p.U, p.W)
            assert evaluate(counter_state) == (a if n == 0 else n - 1)
            identities += 3
    cli_checks = 0
    for flag in [[], ['-O']]:
        for doc in accepted_docs[:5] + invalid:
            result = subprocess.run([sys.executable, *flag, str(HERE / 'counter_name3_matched.py')],
                                    input=json.dumps(doc), text=True, capture_output=True)
            actual = result.returncode == 0 and result.stdout.strip() == 'ACCEPT'
            assert actual == accepted(doc)
            cli_checks += 1
    names = ['counter_name3_matched.py', 'incoming_output_control.py',
             'counter_name3_fuel.py', 'incoming_output_control_fuel.py']
    size_report = {name: metrics(HERE / name) for name in names}
    (HERE / 'metrics.json').write_text(json.dumps(size_report, indent=2) + '\n')
    report = {'python': sys.version, 'accepted_examples': len(examples),
              'translated_uniform_examples': translated, 'translation_skips': skipped,
              'goal_directed_replays': replays, 'invalid_documents_rejected': len(invalid),
              'malformed_fuel_rejected': malformed_fuel,
              'exact_and_one_less_fuel_checks': 2 * len(examples),
              'cli_checks': cli_checks, 'independent_numerical_checks': semantic_checks,
              'generated_normal_form_idempotence_checks': generated,
              'selector_and_recursor_checks': identities, 'state_first_capture_mutant_detected': True,
              'two_parameter_open_sequent_passed': True, 'fuel_costs': fuel_costs}
    (HERE / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'fuel_costs'}, indent=2))
    print(json.dumps(size_report, indent=2))


if __name__ == '__main__':
    main()
