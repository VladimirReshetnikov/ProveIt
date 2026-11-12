"""Reproduce checker metrics, certificate translations, and finite regressions."""
import ast
import copy
import gzip
import hashlib
import io
import itertools
import json
from pathlib import Path
import platform
import random
import subprocess
import sys
import tokenize
import zlib

import control_eight as old
import zero_seven as seven
import zero_six as six
import translate

ROOT = Path(__file__).resolve().parent
Z = ['z']
V = ['v', 0]
ONE = ['s', Z]


def metrics(path):
    raw = path.read_bytes()
    normalized = ast.unparse(ast.parse(raw.decode())) + '\n'
    data = normalized.encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
               tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}
    return dict(raw_bytes=len(raw), normalized_bytes=len(data),
                significant_tokens=sum(t.type not in ignored for t in
                    tokenize.generate_tokens(io.StringIO(normalized).readline)),
                ast_nodes=sum(1 for _ in ast.walk(ast.parse(normalized))),
                gzip9_bytes=len(gzip.compress(data, compresslevel=9, mtime=0)),
                source_sha256=hashlib.sha256(raw).hexdigest())


def run_cli(module, certificate, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / module)]
    result = subprocess.run(command, input=json.dumps(certificate), capture_output=True,
                            text=True, timeout=20)
    return result.returncode == 0 and result.stdout == 'ACCEPT\n'


def certificate(proof, n=0, context=None):
    context = [] if context is None else context
    return dict(variables=n, context=context, proof=proof,
                goal=seven.infer(proof, context, n))


def extra_cases():
    yield 'closed_reflexivity', certificate(translate.reflexivity(ONE))
    yield 'open_reflexivity', certificate(translate.reflexivity(V), 1)
    # The base assumption is used underneath another eigenvariable. The
    # seven-to-six compiler must weaken its replacement across that scope.
    matrix = ['=', ['v', 2], ['v', 2]]
    dummy = ['di', ['=', Z, Z], Z, ['hyp', 0]]
    step = ['de', ['=', ['v', 1], ['v', 1]], dummy, ['hyp', 1]]
    yield 'case_base_used_under_nested_eigenvariable', certificate(
        ['di', matrix, Z, step], 1)
    # A closed term representing zero survives zero-only normalization.
    alias = translate.ALIAS
    body = ['=', ['v', 1], ['v', 1]]
    yield 'nonliteral_zero_witness', certificate(
        ['di', body, alias, translate.reflexivity(alias)])


def negatives():
    good = certificate(translate.reflexivity(Z))
    redex = ['i', Z, Z, ['s', V]]
    c = copy.deepcopy(good)
    c['goal'] = ['=', redex, Z]
    yield 'nonnormal_goal', c
    c = copy.deepcopy(good)
    c['context'] = [['=', redex, Z]]
    yield 'nonnormal_context', c
    c = copy.deepcopy(good)
    c['proof'] = ['succ', Z, Z, ['i', Z, Z, V]]
    yield 'nonnormal_update_body', c
    c = copy.deepcopy(good)
    c['proof'] = ['tr', ['i', Z, V, Z], good['proof'], good['proof']]
    yield 'nonnormal_transport_template', c
    c = copy.deepcopy(good)
    c['proof'] = ['succ', redex, Z, Z]
    yield 'nonnormal_counter_parameter', c
    c = copy.deepcopy(good)
    c['proof'] = ['succ', Z, redex, Z]
    yield 'nonnormal_seed_parameter', c
    c = copy.deepcopy(good)
    c['goal'] = ['=', ['i', Z, Z, ['v', 999]], Z]
    yield 'nonnormal_hidden_scope_escape', c
    c = copy.deepcopy(good)
    c['variables'] = False
    yield 'boolean_scope', c
    c = copy.deepcopy(good)
    c['goal'] = [False, Z, Z]
    yield 'boolean_formula_tag', c
    c = copy.deepcopy(good)
    c['goal'] = ['=', Z, ONE]
    yield 'false_equation', c
    c = copy.deepcopy(good)
    c['proof'] = ['zero', Z, Z]
    yield 'removed_zero_rule', c
    c = copy.deepcopy(good)
    c['proof'] = ['tr', V, good['proof'], translate.reflexivity(ONE)]
    yield 'mismatched_transport_source', c


def shallow_terms(n):
    base = [Z] + [['v', j] for j in range(n)]
    bodies = [Z] + [['v', j] for j in range(n + 1)]
    return base + [['s', t] for t in base] + [
        ['i', c, a, h] for c, a, h in itertools.product(base, base, bodies)]


def random_term(rng, n, depth):
    if depth == 0:
        return ['v', rng.randrange(n)] if n and rng.randrange(2) else Z
    mode = rng.randrange(4)
    if mode == 0:
        return random_term(rng, n, 0)
    if mode == 1:
        return ['s', random_term(rng, n, depth - 1)]
    return ['i', random_term(rng, n, depth - 1),
            random_term(rng, n, depth - 1), random_term(rng, n + 1, depth - 1)]


def property_checks():
    counts = {'idempotence': 0, 'canonical_scope': 0, 'shift_commutation': 0,
              'substitution_commutation': 0, 'zero_equations': 0,
              'successor_equations': 0, 'formula_root_preservation': 0}
    def check_term(t, n):
        normal = translate.normalize(t)
        if translate.normalize(normal) != normal:
            raise RuntimeError('Normalization not idempotent')
        counts['idempotence'] += 1
        seven.term(normal, n)
        counts['canonical_scope'] += 1
        if translate.normalize(old.shift(t)) != seven.shift(normal):
            raise RuntimeError('Normalization does not commute with shift')
        counts['shift_commutation'] += 1
    def check_sub(a, t, n):
        lhs = translate.normalize(old.sub(a, t))
        rhs = seven.sub(translate.normalize(a), translate.normalize(t))
        if lhs != rhs:
            raise RuntimeError('Normalization does not commute with substitution')
        seven.term(rhs, n)
        counts['substitution_commutation'] += 1
    for n in range(3):
        for t in shallow_terms(n):
            check_term(t, n)
        for a, t in itertools.product(shallow_terms(n + 1), shallow_terms(n)):
            check_sub(a, t, n)
    rng = random.Random(20261111)
    for j in range(400):
        n = j % 4
        t, a = random_term(rng, n, 3), random_term(rng, n + 1, 3)
        check_term(t, n)
        check_sub(a, t, n)
        seed = random_term(rng, n, 2)
        h = random_term(rng, n + 1, 2)
        left0 = translate.normalize(['i', Z, seed, h])
        if left0 != translate.normalize(seed):
            raise RuntimeError('Wrong zero reduction')
        counts['zero_equations'] += 1
        # The surviving IS axiom need not normalize to a reflexive equation;
        # its output must equal normalization of the old axiom's output.
        old_axiom = old.infer(['succ', t, seed, h], [], n)
        new_axiom = seven.infer(['succ', translate.normalize(t),
                                 translate.normalize(seed), translate.normalize(h)], [], n)
        if translate.normalize(old_axiom) != new_axiom:
            raise RuntimeError('IS axiom translation mismatch')
        counts['successor_equations'] += 1
        body = ['=', random_term(rng, n + 2, 2), random_term(rng, n + 2, 2)]
        f = ['d', body]
        nf = translate.normalize(f)
        seven.formula(nf, n)
        if nf[0] != f[0] or nf[1][0] != body[0]:
            raise RuntimeError('Formula-root guard changed')
        counts['formula_root_preservation'] += 1
    return counts


def main():
    cases = []
    for source, suffix, module in [('native', '_native.json', 'upstream_native.py'),
                                   ('one', '_one.json', 'control_eight.py')]:
        for path in sorted((ROOT / 'tests/inherited').glob('*' + suffix)):
            if path.name.startswith('reject_'):
                continue
            c = json.loads(path.read_text())
            canonical = translate.canonical_certificate(c, source)
            minimal = translate.six_certificate(canonical)
            cases.extend([(path.stem + '_source', module, c, True),
                          (path.stem + '_zero_seven', 'zero_seven.py', canonical, True),
                          (path.stem + '_zero_six', 'zero_six.py', minimal, True)])
    for name, c in extra_cases():
        cases.extend([(name + '_seven', 'zero_seven.py', c, True),
                      (name + '_six', 'zero_six.py', translate.six_certificate(c), True)])
    for name, c in negatives():
        for module in ['zero_seven.py', 'zero_six.py']:
            cases.append((name, module, c, False))
    for path in sorted((ROOT / 'tests/inherited').glob('reject_*.json')):
        c = json.loads(path.read_text())
        for module in ['zero_seven.py', 'zero_six.py']:
            cases.append((path.stem, module, c, False))
    records = []
    for optimized in [False, True]:
        for name, module, c, expected in cases:
            actual = run_cli(module, c, optimized)
            records.append(dict(name=name, module=module, optimized=optimized,
                                expected=expected, actual=actual))
            if actual != expected:
                raise RuntimeError(f'Failed {name}, {module}, optimized={optimized}')
    properties = property_checks()
    files = ['upstream_native.py', 'upstream_one_context.py', 'control_eight.py',
             'control_seven.py', 'zero_seven.py', 'zero_six.py']
    report = dict(python=sys.version, platform=platform.platform(), zlib=zlib.ZLIB_VERSION,
                  baseline_commit='ecb3b847290c33b1ef7f04571cac63e97c73a54e',
                  metrics={name: metrics(ROOT / name) for name in files},
                  test_count=len(records), expected_acceptances=sum(r['expected'] for r in records),
                  expected_rejections=sum(not r['expected'] for r in records),
                  mismatches=0, property_checks=properties, records=records,
                  limits=['Finite tests are not universal soundness proofs.',
                          'These are exact tagged-syntax checkers, not 521-byte arity-checker competitors.',
                          'All source certificates are validated before normalization.',
                          'All supplied public and rule-parameter syntax must already be zero-normal.',
                          'The trusted normalizer performs only structural I(0,a;u.h) erasure.',
                          'The untrusted compiler may duplicate proof trees.'])
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ['test_count', 'expected_acceptances',
                                           'expected_rejections', 'mismatches',
                                           'property_checks', 'metrics']}, indent=2))


if __name__ == '__main__':
    main()
