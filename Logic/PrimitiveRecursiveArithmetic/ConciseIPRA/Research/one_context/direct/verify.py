"""Reproduce exact whole-module metrics and finite regression evidence."""
import ast
import copy
import gzip
import hashlib
import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tokenize

import native_checker as native
import one_context_checker as one
from translate import native_refl, translate, translate_certificate

ROOT = Path(__file__).resolve().parent
Z = ['z']
V = ['v', 0]
SV = ['s', V]


def certificate(proof, n=0, context=None):
    context = [] if context is None else context
    return dict(variables=n, context=context, goal=native.infer(proof, context, n), proof=proof)


def identity_equation():
    return ['=', ['i', V, Z, SV], V]


def identity_closure_proof():
    lhs = ['i', SV, Z, SV]
    step = ['tr', native.shift(lhs), SV, ['hyp', 0], ['succ', V, Z, SV]]
    return ['qi', identity_equation(), step]


def random_term(rng, n, depth):
    if depth == 0:
        return ['v', rng.randrange(n)] if n and rng.randrange(2) else Z
    choice = rng.randrange(4)
    if choice == 0:
        return random_term(rng, n, 0)
    if choice == 1:
        return ['s', random_term(rng, n, depth - 1)]
    return ['i', random_term(rng, n, depth - 1), random_term(rng, n, depth - 1),
            random_term(rng, n + 1, depth - 1)]


def evaluate(t, environment, fuel):
    """Independent standard-N semantics, with a test-only iteration budget."""
    if fuel[0] <= 0:
        raise TimeoutError
    fuel[0] -= 1
    tag = t[0]
    if tag == 'v':
        return environment[t[1]]
    if tag == 'z':
        return 0
    if tag == 's':
        return 1 + evaluate(t[1], environment, fuel)
    count = evaluate(t[1], environment, fuel)
    value = evaluate(t[2], environment, fuel)
    if count > 1000:
        raise TimeoutError
    for _ in range(count):
        value = evaluate(t[3], [value] + environment, fuel)
    return value


def metrics(path):
    source = path.read_text()
    tree = ast.parse(source)
    normalized = ast.unparse(tree) + '\n'
    encoded = normalized.encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT, tokenize.DEDENT,
               tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}
    return dict(raw_bytes=len(source.encode()), normalized_bytes=len(encoded),
                significant_tokens=sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
                ast_nodes=sum(1 for _ in ast.walk(ast.parse(normalized))),
                gzip9_bytes=len(gzip.compress(encoded, compresslevel=9, mtime=0)),
                source_sha256=hashlib.sha256(source.encode()).hexdigest())


def run_cli(module, c, optimized=False):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / module)]
    result = subprocess.run(command, input=json.dumps(c), capture_output=True, text=True, timeout=10)
    return result.returncode == 0 and result.stdout == 'ACCEPT\n'


def main():
    rng = random.Random(20261111)
    positive = []
    nested = ['i', ['s', ['s', Z]], ['s', Z], ['i', V, ['s', V], ['s', V]]]
    positive.append(('nested_reflexivity', certificate(native_refl(nested))))
    positive.append(('used_hypothesis_induction', certificate(identity_closure_proof())))
    positive.append(('closure_at_nested_iterator', certificate(['qe', nested, identity_closure_proof(), ['zero', Z, SV]])))
    di = ['di', identity_equation(), Z, ['qe', SV, identity_closure_proof(), ['hyp', 0]]]
    positive.append(('dependent_case_from_closure', certificate(di)))
    positive.append(('existential_elimination', certificate(['de', ['q', identity_equation()], di, ['hyp', 0]])))
    double = ['di', ['d', identity_equation()], Z, ['hyp', 0]]
    positive.append(('nested_compound_binders', certificate(double)))
    positive.append(('nested_compound_elimination', certificate(['de', ['q', ['d', identity_equation()]], double, ['hyp', 0]])))
    b = ['=', ['i', Z, ['v', 1], ['s', ['v', 1]]], ['v', 1]]
    a = native.sub(['q', b], nested)[1]
    step_goal = native.sub(a, SV, 0)
    positive.append(('capture_avoiding_witness', certificate(['di', b, nested, ['zero', step_goal[1][2], step_goal[1][3]]])))
    for k in range(24):
        n = 1 + k % 4
        s, t = random_term(rng, n, 2), random_term(rng, n, 2)
        a, b = random_term(rng, n + 1, 3), random_term(rng, n + 1, 3)
        g = [['=', s, t], ['=', native.sub(a, s), native.sub(b, s)]]
        positive.append((f'open_transport_{k:02}', certificate(['tr', a, b, ['hyp', 0], ['hyp', 1]], n, g)))

    destination = ROOT / 'certificates'
    destination.mkdir(exist_ok=True)
    outcomes = []
    for name, original in positive:
        changed = translate_certificate(original, 'native')
        one.check(changed)
        roundtrip = translate_certificate(changed, 'one')
        native.check(roundtrip)
        if original['goal'] != changed['goal'] or original['goal'] != roundtrip['goal']:
            raise RuntimeError('Translation changed the statement')
        for version, module, c in [('native', 'native_checker.py', original),
                                   ('one', 'one_context_checker.py', changed),
                                   ('roundtrip', 'native_checker.py', roundtrip)]:
            (destination / f'{name}_{version}.json').write_text(json.dumps(c, separators=(',', ':')) + '\n')
            for optimized in [False, True]:
                ok = run_cli(module, c, optimized)
                outcomes.append(dict(name=name, version=version, optimized=optimized, expected=True, accepted=ok))
                if not ok:
                    raise RuntimeError(f'Valid certificate rejected: {name}, {version}, -O={optimized}')

    negatives = []
    good = positive[0][1]
    def mutated(name, function):
        c = copy.deepcopy(good)
        function(c)
        negatives.append((name, c))
    mutated('boolean_variable_count', lambda c: c.update(variables=True))
    mutated('free_variable_goal', lambda c: c.update(goal=['=', V, V]))
    mutated('unknown_rule', lambda c: c.update(proof=['untrusted', c['goal']]))
    mutated('extra_top_level_field', lambda c: c.update(oracle=True))
    mutated('forged_zero_computation', lambda c: c.update(proof=['zero', Z, Z], goal=['=', Z, ['s', Z]]))
    mutated('boolean_hypothesis_index', lambda c: c.update(context=[c['goal']], proof=['hyp', False]))
    mutated('negative_hypothesis_index', lambda c: c.update(context=[c['goal']], proof=['hyp', -1]))
    mutated('de_eigenvariable_escape', lambda c: c.update(proof=['de', ['=', V, V], di, ['hyp', 0]]))
    mutated('di_witness_escape', lambda c: c.update(proof=['di', b, V, ['hyp', 0]]))
    mutated('compound_induction', lambda c: c.update(proof=['qi', ['d', identity_equation()], ['hyp', 0]]))
    mutated('wrong_closure_base', lambda c: c.update(proof=['qe', Z, identity_closure_proof(), ['zero', ['s', Z], Z]]))
    leaked = dict(variables=1, context=[['=', V, Z]], goal=['q', ['=', V, Z]],
                  proof=['qi', ['=', V, Z], ['hyp', 1]])
    negatives.append(('unshifted_context_induction_attack', leaked))
    for name, c in negatives:
        (destination / f'reject_{name}.json').write_text(json.dumps(c, separators=(',', ':')) + '\n')
        for module in ['native_checker.py', 'one_context_checker.py']:
            submitted = c
            if name == 'wrong_closure_base' and module == 'one_context_checker.py':
                submitted = copy.deepcopy(c)
                submitted['proof'][2] = translate(identity_closure_proof(), 'native', [], 0)
                (destination / f'reject_{name}_one.json').write_text(json.dumps(submitted, separators=(',', ':')) + '\n')
            for optimized in [False, True]:
                accepted = run_cli(module, submitted, optimized)
                outcomes.append(dict(name=name, version=module, optimized=optimized, expected=False, accepted=accepted))
                if accepted:
                    raise RuntimeError(f'Invalid certificate accepted: {name}, {module}, -O={optimized}')

    semantic = 0
    skipped = 0
    for _ in range(300):
        n = 1 + rng.randrange(4)
        t = random_term(rng, n + 1, 3)
        image = random_term(rng, n, 2)
        environment = [rng.randrange(3) for _ in range(n)]
        try:
            value = evaluate(image, environment, [30000])
            left = evaluate(native.sub(t, image), environment, [30000])
            right = evaluate(t, [value] + environment, [30000])
        except TimeoutError:
            skipped += 1
            continue
        if left != right:
            raise RuntimeError('Substitution disagrees with independent numeric semantics')
        semantic += 1
    report = dict(python=sys.version, positive_theorems=len(positive), negative_fixtures=len(negatives),
                  cli_checks=len(outcomes), mismatches=sum(x['expected'] != x['accepted'] for x in outcomes),
                  semantic_substitution_checks=semantic, semantic_budget_skips=skipped,
                  metrics={name: metrics(ROOT / name) for name in ['native_checker.py', 'one_context_checker.py']},
                  outcomes=outcomes,
                  boundary='Finite implementation tests; Lean files are uncompiled. No global minimality claim.')
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'outcomes'}, indent=2))


if __name__ == '__main__':
    main()
