"""Reproduce finite validation and complete-module source measurements.

No finite test below establishes a universal equivalence theorem. The report's
written derivations provide those proofs. All producers and translators here
are untrusted and are absent from every standalone checker.
"""
import ast
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tokenize

from proofs import Builder, ONE, fixture, iterator, opening, positive_fixtures
from translate import kernel, transform, translate_certificate

ROOT = Path(__file__).resolve().parent


def load_file(name):
    spec = importlib.util.spec_from_file_location(name.replace('.', '_'), ROOT / name)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def measurements(path):
    tree = ast.parse(path.read_text())
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.body and isinstance(node.body[0], ast.Expr):
                value = node.body[0].value
                if isinstance(value, ast.Constant) and isinstance(value.value, str):
                    node.body.pop(0)
    normalized = (ast.unparse(tree) + '\n').encode()
    ignored = {tokenize.COMMENT, tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE,
               tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
    tokens = sum(t.type not in ignored for t in
                 tokenize.generate_tokens(io.StringIO(normalized.decode()).readline))
    return {'normalized_bytes': len(normalized), 'significant_tokens': tokens,
            'ast_nodes': len(list(ast.walk(tree))),
            'gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
            'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def negative_fixtures():
    good = fixture(Builder('seed').refl(0))
    cases = {}
    for name, value in [('boolean', True), ('float', 0.0), ('null', None),
                        ('string', '0'), ('mapping', {}), ('negative_escape', -1),
                        ('positive_escape', 1), ('zero_counter', ['i', 0, 0, 1]),
                        ('body_escape', ['i', ONE, 0, 2])]:
        cases['bad_term_' + name] = {'goal': ['=', value, value], 'proof': ['r', value]}
    cases['wrong_top_keys'] = dict(good, extra=0)
    cases['bad_proof_tag'] = {'goal': good['goal'], 'proof': ['unknown', 0]}
    cases['extra_proof_field'] = {'goal': good['goal'], 'proof': ['r', 0, 0]}
    cases['no_iterator_minor'] = {'goal': good['goal'], 'proof': ['x', ['r', 0], ['r', 0]]}
    cases['wrong_initializer'] = {
        'goal': ['=', iterator(['s', ONE], ONE, 1), ONE],
        'proof': ['x', ['r', 0], ['r', iterator(['s', ONE], ONE, 1)]],
    }
    cases['forgot_preceding_iterations'] = {
        'goal': ['=', iterator(['s', ONE], 0, ['s', 1]), ONE],
        'proof': ['x', ['r', 0], ['r', iterator(['s', ONE], 0, ['s', 1])]],
    }
    goal = ['d', ['=', 1, 1]]
    proof = ['i', goal, 0, ['r', ['s', -1]]]
    cases['di_witness_escape'] = {'goal': goal, 'proof': ['i', goal, -1, ['r', ['s', -1]]]}
    cases['de_goal_escape'] = {'goal': ['=', -1, -1], 'proof': ['e', ['=', -1, -1], proof, ['r', -1]]}
    for name, index in [('negative', -1), ('boolean', True), ('high', 1)]:
        cases['bad_clause_index_' + name] = {
            'goal': ['=', ONE, ONE],
            'proof': ['e', ['=', ONE, ONE], proof, ['u', index, ONE, ['r', 0]]],
        }
    cases['wrong_clause_antecedent'] = {
        'goal': ['=', ONE, ONE],
        'proof': ['e', ['=', ONE, ONE], proof, ['u', 0, ONE, ['r', ONE]]],
    }
    cases['false_equation'] = {'goal': ['=', 0, ONE], 'proof': ['r', 0]}
    cases['proof_not_array'] = {'goal': good['goal'], 'proof': {'r': 0}}
    return cases


def value(a, free, bound):
    if type(a) is int:
        return 0 if a == 0 else free[-a - 1] if a < 0 else bound[-a]
    if a[0] == 's':
        return 1 + value(a[1], free, bound)
    result = value(a[2], free, bound)
    for _ in range(value(a[1], free, bound)):
        result = value(a[3], free, bound + [result])
    return result


def random_term(rng, depth, fuel):
    if not fuel or rng.randrange(3) == 0:
        return rng.choice([0, -1, -2] + list(range(1, depth + 1)))
    if rng.randrange(3) == 0:
        return ['s', random_term(rng, depth, fuel - 1)]
    counter = rng.choice([ONE, ['s', ONE], -1])
    return ['i', counter, random_term(rng, depth, fuel - 1),
            random_term(rng, depth + 1, fuel - 1)]


def arith_count(proof):
    match proof:
        case ['x', major, minor]:
            return 1 + arith_count(major) + arith_count(minor)
        case ['u', index, witness, premise]:
            return arith_count(premise)
        case ['e', goal, data, branch]:
            return arith_count(data) + arith_count(branch)
        case ['i', goal, data, branch]:
            return arith_count(branch)
    return 0


def run_process(name, certificate, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / name)]
    result = subprocess.run(command, input=json.dumps(certificate), text=True,
                            capture_output=True, timeout=20)
    return result.returncode == 0 and result.stdout == 'ACCEPT\n'


def main():
    seed = kernel('seed')
    step = kernel('step')
    seed_literal = load_file('seed_literal.py')
    step_literal = load_file('control_step_literal.py')
    counts = {'generated_positive_cases': 0, 'pinned_upstream_cases': 0,
              'matched_literal_positive_pairs': 0, 'translations': 0,
              'round_trips': 0, 'negative_rejections': 0,
              'semantic_opening_checks': 0, 'semantic_seed_checks': 0,
              'open_translation_checks': 0, 'passive_parameter_checks': 0,
              'public_processes': 0}
    new_cases = positive_fixtures('seed')
    for mode in ('seed', 'step', 'control'):
        for c in positive_fixtures(mode).values():
            kernel(mode).verify(c)
            counts['generated_positive_cases'] += 1
    upstream = {p.stem: json.loads(p.read_text())
                for p in sorted((ROOT / 'fixtures' / 'upstream_step').glob('*.json'))}
    for name, c in upstream.items():
        step.verify(c)
        step_literal.verify(c)
        counts['pinned_upstream_cases'] += 1
        counts['matched_literal_positive_pairs'] += 1
    for c in new_cases.values():
        seed.verify(c)
        seed_literal.verify(c)
        counts['matched_literal_positive_pairs'] += 1

    for source, target, cases in [('step', 'seed', upstream), ('seed', 'step', new_cases)]:
        directory = ROOT / 'fixtures' / (source + '_to_' + target)
        directory.mkdir(parents=True, exist_ok=True)
        for name, c in cases.items():
            translated = translate_certificate(c, source, target)
            (directory / (name + '.json')).write_text(json.dumps(translated, separators=(',', ':')) + '\n')
            counts['translations'] += 1
            returned = translate_certificate(translated, target, source)
            assert returned['goal'] == c['goal']
            counts['round_trips'] += 1

    negatives = negative_fixtures()
    for c in negatives.values():
        for k in (seed, seed_literal, step, step_literal):
            try:
                k.verify(c)
            except Exception:
                counts['negative_rejections'] += 1
            else:
                raise AssertionError(('accepted negative', k.__name__, c))

    rng = random.Random(20261112)
    for depth in range(3):
        for _ in range(180):
            a = random_term(rng, depth + 1, 3)
            image = random_term(rng, 0, 2)
            out = seed.opening(a, image, depth)
            assert out == opening(a, image, depth) == seed_literal.opening(a, image, depth)
            seed.syntax(out, 2, depth)
            free = [rng.randrange(2), rng.randrange(2)]
            locals = [rng.randrange(2) for _ in range(depth)]
            assert value(out, free, locals) == value(a, free, [value(image, free, [])] + locals)
            counts['semantic_opening_checks'] += 1
    for _ in range(180):
        n = rng.choice([0, ONE, ['s', ONE], -1])
        a = random_term(rng, 0, 2)
        b = iterator(ONE, a, 1)
        h = random_term(rng, 1, 2)
        free = [rng.randrange(2), rng.randrange(2)]
        lhs = iterator(['s', n], a, h)
        rhs = opening(h, iterator(n, b, h))
        assert value(a, free, []) == value(b, free, [])
        assert value(lhs, free, []) == value(rhs, free, [])
        counts['semantic_seed_checks'] += 1

    overheads = {}
    for source, target in [('seed', 'step'), ('step', 'seed')]:
        for counter in (0, -3):
            a, b, r = -1, -2, -4
            h = ['s', 1]
            major_source = a if source == 'seed' else iterator(counter, a, h)
            major_formula = ['=', major_source, b]
            minor_formula = ['=', iterator(['s', counter], a, h), r]
            context = [(['=', 0, 0], major_formula), (['=', 0, 0], minor_formula)]
            p = ['x', ['u', 0, 0, ['r', 0]], ['u', 1, 0, ['r', 0]]]
            expected = kernel(source).derive(p, context, 4)
            translated = transform(p, source, target, context, 4)
            assert kernel(target).derive(translated, context, 4) == expected
            overheads[source + '_to_' + target + ('_zero' if counter == 0 else '_general')] = arith_count(translated)
            counts['open_translation_checks'] += 1
    assert overheads == {'seed_to_step_zero': 1, 'seed_to_step_general': 3,
                         'step_to_seed_zero': 1, 'step_to_seed_general': 7}

    # The counter and update contain the old seed as a passive parameter.
    # Only the initializer slot is replaced by the new right endpoint.
    for counter in (0, ['s', -1], iterator(ONE, -1, 1)):
        h = iterator(1, -1, iterator(2, 1, ['s', 1]))
        q = ['=', iterator(['s', counter], -1, h), -4]
        context = [(['=', 0, 0], ['=', -1, -2]), (['=', 0, 0], q)]
        p = ['x', ['u', 0, 0, ['r', 0]], ['u', 1, 0, ['r', 0]]]
        expected = ['=', -4, opening(h, iterator(counter, -2, h))]
        assert seed.derive(p, context, 4) == expected
        assert seed_literal.derive(p, context, 4) == expected
        translated = transform(p, 'seed', 'step', context, 4)
        assert step.derive(translated, context, 4) == expected
        counts['passive_parameter_checks'] += 1
    builder = Builder('seed')
    a = ONE
    equal_seed = builder.sym(builder.comp(0, a, 1))
    counter = iterator(ONE, a, 1)
    h = iterator(1, a, iterator(2, 1, ['s', 1]))
    special = fixture(builder.seed(equal_seed, builder.refl(iterator(['s', counter], a, h))))
    seed.verify(special)
    seed_literal.verify(special)
    new_cases['fixed_counter_and_body'] = special
    zero_seed = builder.comp(0, 0, 1)
    h = iterator(1, ONE, ['s', 1])
    contracted = fixture(builder.seed(zero_seed,
                                     builder.refl(iterator(ONE, zero_seed[0], h))))
    assert contracted['goal'][2] == ONE
    seed.verify(contracted)
    new_cases['zero_counter_nested_contraction'] = contracted

    outputs = ROOT / 'fixtures' / 'seed'
    outputs.mkdir(parents=True, exist_ok=True)
    for name, c in new_cases.items():
        (outputs / (name + '.json')).write_text(json.dumps(c, separators=(',', ':')) + '\n')
    bad_dir = ROOT / 'fixtures' / 'negative'
    bad_dir.mkdir(parents=True, exist_ok=True)
    for name, c in negatives.items():
        (bad_dir / (name + '.json')).write_text(json.dumps(c, separators=(',', ':')) + '\n')

    for name, cases, expected in [('checker.py', new_cases, True),
                                  ('control_step.py', upstream, True),
                                  ('checker.py', negatives, False)]:
        for c in cases.values():
            for optimized in (False, True):
                assert run_process(name, c, optimized) == expected
                counts['public_processes'] += 1
    selected = list(new_cases.values())[:6] + [special, contracted]
    for c in selected:
        for optimized in (False, True):
            assert run_process('seed_literal.py', c, optimized)
            counts['public_processes'] += 1

    files = ['checker.py', 'control_step.py', 'seed_literal.py',
             'control_step_literal.py', 'control_computation_transport.py']
    metrics = {name: measurements(ROOT / name) for name in files}
    costs = []
    for counter in (0, ONE, ['s', ONE]):
        h = iterator(1, ONE, iterator(2, 1, ['s', 1]))
        row = {'counter': counter}
        for mode in ('step', 'seed'):
            cert = fixture(Builder(mode).comp(counter, ONE, h))
            row[mode + '_json_bytes'] = len(json.dumps(cert, separators=(',', ':')).encode())
            row[mode + '_arithmetic_instances'] = arith_count(cert['proof'])
        costs.append(row)
    report = {'python': sys.version, 'counts': counts, 'metrics': metrics,
              'translated_arithmetic_instances': overheads, 'computation_certificate_sizes': costs,
              'status': 'All finite checks passed',
              'limitations': ['No new proof-assistant verification.',
                              'Finite testing does not prove the universal metatheorems.',
                              'Literal shipped style ties; the shared-walk arithmetic change saves two bytes and two tokens only.',
                              'The 516-byte compact and 788-byte goal-validated historical profiles remain smaller.']}
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
