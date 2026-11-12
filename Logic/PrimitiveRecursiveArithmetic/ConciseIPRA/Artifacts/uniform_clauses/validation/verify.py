"""Reproduce the Horn-clause reduction and its complete-program checks.

Finite tests supplement the written metatheorems. They do not constitute
proof-assistant verification of soundness or bi-interpretability.
"""
import ast
import copy
import gzip
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

import clausal_eval as legacy
import clausal_eval_shared as legacy_shared
import clausal_eval_two as two
import clausal_eval_two_shared as two_shared
import clausal_horn_shared as horn
from identity_translate import to_two, from_two, transform
from horn_translate import to_horn, from_horn, _proof, REFLEXIVITY

ROOT = Path(__file__).resolve().parent


def accepted(checker, data):
    try:
        checker.verify(data)
        return True
    except Exception:
        return False


def legacy_certificate(proof):
    return {'goal': legacy.derive(proof, [], 0), 'proof': proof}


def sym(proof, context=None, scope=0):
    context = [] if context is None else context
    s, t = legacy.derive(proof, context, scope)
    return ['v', ['r', s], proof]


def congruence(template, proof, source):
    a = [0, source, template]
    b = [[0, 0], source, template]
    zero = ['v', ['r', source], ['r', a]]
    first = ['v', zero, ['r', b]]
    second = ['v', proof, ['r', a]]
    return ['v', second, first]


def node_count(proof):
    if not isinstance(proof, list) or not proof or not isinstance(proof[0], str):
        return 0
    tag = proof[0]
    if tag == 'r':
        return 1
    if tag == 'u':
        payload = proof[3]
        if payload and isinstance(payload[0], str):
            return 1 + node_count(payload)
        return 1 + sum(node_count(p) for p in payload)
    if tag == 'v':
        return 1 + node_count(proof[1]) + node_count(proof[2])
    if tag == 'e':
        return 1 + node_count(proof[2]) + node_count(proof[3])
    return 1 + node_count(proof[3])


def make_cases():
    manifest = json.loads((ROOT / 'fixtures/legacy/manifest.json').read_text())
    positives = {}
    for row in manifest:
        data = json.loads((ROOT / 'fixtures/legacy' / (row['name'] + '.json')).read_text())
        if accepted(legacy, data) != row['accept'] or accepted(legacy_shared, data) != row['accept']:
            raise RuntimeError('published/matched baseline mismatch: ' + row['name'])
        if row['accept']:
            positives[row['name']] = data

    z = [0, 0, 1]
    p = ['v', ['r', 0], ['r', z]]
    positives['explicit_symmetry'] = legacy_certificate(sym(p))
    positives['explicit_transitivity'] = legacy_certificate(['v', sym(p), sym(p)])
    positives['explicit_successor_congruence'] = legacy_certificate(congruence([0, 1], p, z))
    positives['eq_case_nonzero_witness'] = legacy_certificate(
        ['i', [[[1, 2, 3], 2]], [0, 0],
         ['v', ['r', [-1, [0, 0], [0, 0]]],
          ['r', [[0, -1], [0, 0], [0, 0]]]]])
    d = ['i', [[2, 2]], [0, 0], ['r', [0, 0]]]
    use = ['u', 0, 0, ['r', -1]]
    positives['witness_dependent_elimination'] = legacy_certificate(
        ['e', [0, 0], d, congruence(0, use, -1)])

    converted = {}
    transforms = []
    for name, data in positives.items():
        middle = to_two(data)
        from_two(middle)
        two_shared.verify(middle)
        target = to_horn(middle)
        back = from_horn(target)
        again = to_horn(back)
        if not (data['goal'] == middle['goal'] == target['goal'] == back['goal'] == again['goal']):
            raise RuntimeError('changed end formula: ' + name)
        legacy_shared.verify(back)
        converted[name] = target
        transforms.append({'name': name, 'legacy_nodes': node_count(data['proof']),
                           'eval2_nodes': node_count(middle['proof']),
                           'horn_nodes': node_count(target['proof']),
                           'roundtrip_nodes': node_count(back['proof'])})

    r = lambda t: ['u', 0, t, []]
    base = {'goal': [0, 0], 'proof': r(0)}
    rejects = {
        'extra_top_field': dict(base, extra=0),
        'missing_top_field': {'goal': [0, 0]},
        'boolean_term': {'goal': [False, False], 'proof': r(False)},
        'boolean_successor_tag': {'goal': [[False, 0], [False, 0]], 'proof': r([False, 0])},
        'float_term': {'goal': [0.0, 0.0], 'proof': r(0.0)},
        'null_term': {'goal': [None, None], 'proof': r(None)},
        'free_parameter': {'goal': [-1, -1], 'proof': r(-1)},
        'loose_bound_index': {'goal': [1, 1], 'proof': r(1)},
        'unknown_rule': {'goal': [0, 0], 'proof': ['unknown', 0]},
        'old_reflexivity_tag': {'goal': [0, 0], 'proof': ['r', 0]},
        'extra_rule_field': {'goal': [0, 0], 'proof': ['u', 0, 0, [], 0]},
        'nonlist_use_payload': {'goal': [0, 0], 'proof': ['u', 0, 0, None]},
        'extra_nullary_premise': {'goal': [0, 0], 'proof': ['u', 0, 0, [r(0)]]},
        'malformed_nullary_premise': {'goal': [0, 0], 'proof': ['u', 0, 0, ['ignored']]},
        'forged_false_goal': {'goal': [0, [0, 0]], 'proof': r(0)},
        'nonexistent_clause': {'goal': [0, 0], 'proof': ['u', 1, 0, []]},
        'boolean_clause_index': {'goal': [0, 0], 'proof': ['u', False, 0, []]},
        'negative_clause_index': {'goal': [0, 0], 'proof': ['u', -1, 0, []]},
        'removed_identity_eval_case': {'goal': [0, 0], 'proof': ['v', r(0), r(0)]},
        'eval_scalar_mismatch': {'goal': [0, 0], 'proof': ['v', r([0, 0]), r(0)]},
        'eval_successor_as_iterator': {'goal': [0, 0], 'proof': ['v', r(0), r([0, 0])]},
        'eval_wrong_zero_source': {'goal': [0, 0], 'proof': ['v', r([0, 0]), r([0, 0, 1])]},
        'witness_eigenvariable_escape': {'goal': [[0, 0]], 'proof': ['i', [[0, 0]], -1, r(0)]},
        'counter_variable_is_not_successor': {'goal': [[0, 0]],
            'proof': ['i', [[0, 0]], 0, ['v', r(0), r([-1, 0, 1])]]},
        'elimination_nonpaired_major': {'goal': [0, 0], 'proof': ['e', [0, 0], r(0), r(0)]},
    }
    dproof = converted['used_induction_hypothesis']['proof']
    rejects['eval_compound_major'] = {'goal': [0, 0], 'proof': ['v', dproof, r(0)]}
    rejects['elimination_eigenvariable_escape'] = {
        'goal': [0, 0], 'proof': ['e', [0, 0], dproof, r(-1)]}
    rejects['elimination_fresh_out_of_scope'] = {
        'goal': [0, 0], 'proof': ['e', [0, 0], dproof, r(-2)]}
    counter = [0, 0, 1]
    source = [0, 0, [0, 1]]
    bad = [counter, 0, [0, 1]]
    rejects['iterator_counter_is_not_successor'] = {
        'goal': [bad, [0, source]], 'proof': ['v', r(source), r(bad)]}
    mutation = copy.deepcopy(converted['used_induction_hypothesis'])
    mutation['proof'][2] = [0, 0]
    rejects['progress_cannot_be_retagged_as_cases'] = mutation

    def mutate_conditional_use(proof, change):
        if isinstance(proof, list):
            if proof and proof[0] == 'u' and isinstance(proof[3], list) and len(proof[3]) == 1:
                proof[3] = change(proof[3])
                return True
            return any(mutate_conditional_use(p, change) for p in proof)
        return False

    for name, change in [('wrong_clause_antecedent', lambda p: [r([0, 0])]),
                         ('missing_clause_antecedent', lambda p: []),
                         ('duplicate_clause_antecedent', lambda p: p + p)]:
        mutation = copy.deepcopy(converted['closure_specialization_4'])
        if not mutate_conditional_use(mutation['proof'], change):
            raise RuntimeError('conditional clause was not exercised')
        rejects[name] = mutation

    # The branch is valid from B(z), but compound introduction must assume B(0).
    compound = json.loads((ROOT / 'fixtures/legacy/compound_progress_is_not_primitive.json').read_text())
    bz = [[-1, -1]]
    old_context = [([0, 0], bz)]
    new_context = [REFLEXIVITY, ([], bz)]
    branch2 = transform(compound['proof'][3], old_context, 1)
    branch4 = _proof(branch2, old_context, new_context, 1, True)
    intended = [[[0, -1], [0, -1]]]
    if horn.derive(branch4, new_context, 1) != intended:
        raise RuntimeError('compound-progress control branch is not valid')
    rejects['compound_progress_is_not_primitive'] = {
        'goal': compound['goal'], 'proof': ['i', compound['goal'], 0, branch4]}

    for name, data in rejects.items():
        if accepted(horn, data):
            raise RuntimeError('accepted adversarial certificate: ' + name)
    return positives, converted, rejects, transforms, manifest


def measure(name):
    path = ROOT / (name + '.py')
    tree = ast.parse(path.read_text())
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.body and isinstance(node.body[0], ast.Expr) and isinstance(node.body[0].value, ast.Constant) and isinstance(node.body[0].value.value, str):
                node.body.pop(0)
    normalized = ast.unparse(tree) + '\n'
    tokens = sum(t.type not in (tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
                               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT)
                 for t in tokenize.generate_tokens(io.StringIO(normalized).readline))
    output = ROOT / 'evidence' / (name + '.normalized.py')
    output.write_text(normalized)
    return {'program': name, 'normalized_bytes': len(normalized.encode()),
            'significant_tokens': tokens, 'ast_nodes': len(list(ast.walk(tree))),
            'gzip9_bytes': len(gzip.compress(normalized.encode(), compresslevel=9, mtime=0))}


def run(path, data, expected, optimize=False, raw=False):
    command = [sys.executable] + (['-O'] if optimize else []) + [str(path)]
    result = subprocess.run(command, input=data if raw else json.dumps(data), text=True,
                            capture_output=True, timeout=10)
    if (result.returncode == 0) != expected or result.stdout != ('ACCEPT\n' if expected else 'REJECT\n'):
        raise RuntimeError(f'public interface mismatch: {path.name}: {result.returncode}: {result.stdout}')


def main():
    (ROOT / 'evidence').mkdir(exist_ok=True)
    positives, converted, rejects, transforms, manifest = make_cases()
    metrics = [measure(name) for name in ('clausal_eval', 'clausal_eval_shared',
               'clausal_eval_two', 'clausal_eval_two_shared', 'clausal_horn_shared')]
    runs = 0
    for optimized in (False, True):
        for name, data in converted.items():
            run(ROOT / 'clausal_horn_shared.py', data, True, optimized)
            run(ROOT / 'evidence/clausal_horn_shared.normalized.py', data, True, optimized)
            run(ROOT / 'clausal_eval_two_shared.py', from_horn(data), True, optimized)
            runs += 3
        for name, data in rejects.items():
            run(ROOT / 'clausal_horn_shared.py', data, False, optimized)
            run(ROOT / 'evidence/clausal_horn_shared.normalized.py', data, False, optimized)
            runs += 2
        for raw in ('{', '', 'null', '[]', '0', 'true', '{"goal": [0, 0]}'):
            run(ROOT / 'clausal_horn_shared.py', raw, False, optimized, True)
            runs += 1
        for row in manifest:
            data = json.loads((ROOT / 'fixtures/legacy' / (row['name'] + '.json')).read_text())
            run(ROOT / 'clausal_eval_shared.py', data, row['accept'], optimized)
            runs += 1
    fixtures = ROOT / 'fixtures/horn'
    fixtures.mkdir(exist_ok=True)
    for name, data in converted.items():
        (fixtures / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    for name, data in rejects.items():
        (fixtures / ('reject_' + name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    report = {'python': sys.version, 'positive_theorems': len(converted),
              'adversarial_certificates': len(rejects), 'malformed_documents': 7,
              'public_process_checks': runs, 'legacy_regression_cases': len(manifest),
              'translation_roundtrips': transforms, 'metrics': metrics,
              'proof_status': 'Written metatheorems plus finite executable checks; no new Lean or Rocq formalization.'}
    (ROOT / 'evidence/results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'translation_roundtrips'}, indent=2))


if __name__ == '__main__':
    main()
