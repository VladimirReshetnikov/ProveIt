"""Representative proof translations, scope checks, and malformed inputs."""
import ast
import copy
import gzip
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code'))
import clausal_eval as new
import matched_control as old
import matched_canonical as canonical
from translate import eval_congruence, old_refl, old_sym, old_trans, translate


def certificate(proof, checker=old):
    return {'goal': checker.derive(proof, [], 0), 'proof': proof}


def accepts(checker, data):
    try:
        checker.verify(data)
        return True
    except Exception:
        return False


def node_count(proof):
    tag = proof[0]
    if tag in ('r', 'z', 's'):
        return 1
    if tag == 'u':
        return 1 + node_count(proof[3])
    if tag == 'i':
        return 1 + node_count(proof[3])
    if tag in ('x', 'e'):
        return 1 + node_count(proof[2]) + node_count(proof[3])
    return 1 + node_count(proof[1]) + node_count(proof[2])


def main():
    examples = {}
    terms = [0, [0, 0], [0, [0, 0]], [0, 0, 1],
             [[0, 0], 0, [0, 1]], [0, [0, 0], [1, 0, 2]]]
    for i, t in enumerate(terms):
        examples[f'reflexivity_{i}'] = certificate(old_refl(t))
        examples[f'zero_computation_{i}'] = certificate(['z', t, [0, 1]])
    bodies = [0, 1, [0, 1], [1, 0, 2], [0, 1, [2, 1, [0, 2]]]]
    for i, h in enumerate(bodies):
        examples[f'successor_computation_{i}'] = certificate(['s', 0, 0, h])
        major = ['z', 0, h]
        s, t = old.derive(major, [], 0)
        minor = old_refl(old.opening(h, s))
        examples[f'template_congruence_{i}'] = certificate(['x', h, major, minor])
    major = old_sym(['z', 0, 1], [], 0)
    template = [1, 1, [2, 1, [0, 2]]]
    minor = old_refl(old.opening(template, 0))
    examples['zero_source_nested_template'] = certificate(['x', template, major, minor])

    # E(y) is I(y,0;u.u)=0. Its actual induction assumption is used.
    matrix = [[1, 0, 1], 0]
    paired = [matrix]
    context = [([0, 0], [[-1, 0, 1], 0])]
    hypothesis = ['u', 0, 0, old_refl(0)]
    computation = ['s', -1, 0, 1]
    step = old_trans(computation, hypothesis, context, 1)
    induction = ['i', paired, 0, step]
    examples['used_induction_hypothesis'] = certificate(induction)
    for i, t in enumerate(terms):
        target = [[t, 0, 1], 0]
        branch = ['u', 0, t, ['z', 0, 1]]
        examples[f'closure_specialization_{i}'] = certificate(['e', target, induction, branch])

    # The outer y remains bound beneath an inner D, hence index 3.
    nested_goal = [[[3, 3]]]
    inner_goal = [[[0, -1], [0, -1]]]
    inner = ['i', inner_goal, [0, 0], old_refl([0, -1])]
    examples['nested_compound_binders'] = certificate(['i', nested_goal, 0, inner])

    # A witness with an internally bound variable is inserted beneath I.
    witness = [[0, 0], 0, [0, 1]]
    goal = [[[1, 2, 3], 2]]
    examples['capture_avoiding_witness'] = certificate(
        ['i', goal, witness, ['s', -1, witness, witness]])

    results = []
    translated = {}
    for name, data in examples.items():
        old.verify(data)
        target = translate(data)
        roundtrip = translate(target, False)
        translate(roundtrip)
        if target['goal'] != data['goal'] or roundtrip['goal'] != data['goal']:
            raise RuntimeError('translation changed an end formula')
        if node_count(target['proof']) > 9 * node_count(data['proof']):
            raise RuntimeError('displayed translation bound failed')
        translated[name] = target
        results.append({'name': name, 'status': 'accepted_both_directions',
                        'old_nodes': node_count(data['proof']),
                        'new_nodes': node_count(target['proof'])})

    base = {'goal': [0, 0], 'proof': ['r', 0]}
    rejects = {
        'extra_field': dict(base, extra=0),
        'boolean_scalar': {'goal': [False, False], 'proof': ['r', False]},
        'boolean_successor_tag': {'goal': [[False, 0], [False, 0]],
                                 'proof': ['r', [False, 0]]},
        'float_scalar': {'goal': [0.0, 0.0], 'proof': ['r', 0.0]},
        'free_parameter': {'goal': [-1, -1], 'proof': ['r', -1]},
        'loose_bound_index': {'goal': [1, 1], 'proof': ['r', 1]},
        'unknown_rule': {'goal': [0, 0], 'proof': ['unknown', 0]},
        'extra_rule_argument': {'goal': [0, 0], 'proof': ['r', 0, 0]},
        'forged_goal': {'goal': [0, [0, 0]], 'proof': ['r', 0]},
        'nonexistent_clause': {'goal': [0, 0], 'proof': ['u', 0, 0, ['r', 0]]},
        'boolean_clause_index': {'goal': [0, 0], 'proof': ['u', False, 0, ['r', 0]]},
        'negative_clause_index': {'goal': [0, 0], 'proof': ['u', -1, 0, ['r', 0]]},
        'eval_scalar_mismatch': {'goal': [0, 0],
                                 'proof': ['v', ['r', [0, 0]], ['r', 0]]},
        'eval_successor_as_iterator': {'goal': [0, 0],
                                       'proof': ['v', ['r', 0], ['r', [0, 0]]]},
        'eval_wrong_zero_source': {'goal': [0, 0],
                                   'proof': ['v', ['r', [0, 0]], ['r', [0, 0, 1]]]},
        'witness_eigenvariable_escape': {'goal': [[0, 0]],
                                        'proof': ['i', [[0, 0]], -1, ['r', 0]]},
        'counter_variable_is_not_successor': {'goal': [[0, 0]],
          'proof': ['i', [[0, 0]], 0, ['v', ['r', 0], ['r', [-1, 0, 1]]]]},
    }
    dproof = translated['used_induction_hypothesis']['proof']
    rejects['eval_compound_major'] = {'goal': [0, 0],
                                     'proof': ['v', dproof, ['r', 0]]}
    rejects['elimination_eigenvariable_escape'] = {'goal': [0, 0],
        'proof': ['e', [0, 0], dproof, ['r', -1]]}
    rejects['elimination_fresh_out_of_scope'] = {'goal': [0, 0],
        'proof': ['e', [0, 0], dproof, ['r', -2]]}
    # Omitting Eval's counter-arity check would accept a false equation.
    c = [0, 0, 1]
    s = [0, 0, [0, 1]]
    b = [c, 0, [0, 1]]
    rejects['iterator_counter_is_not_successor'] = {
        'goal': [b, [0, s]], 'proof': ['v', ['r', s], ['r', b]]}
    mutation = copy.deepcopy(translated['used_induction_hypothesis'])
    mutation['proof'][2] = [0, 0]
    rejects['progress_cannot_be_retagged_as_cases'] = mutation

    def change_first_clause_premise(tree):
        if type(tree) is list:
            if tree and tree[0] == 'u':
                tree[3] = ['r', [0, 0]]  # Reflexivity of numeral one.
                return True
            return any(change_first_clause_premise(item) for item in tree)
        return False

    wrong_antecedent = copy.deepcopy(translated['used_induction_hypothesis'])
    if not change_first_clause_premise(wrong_antecedent['proof']):
        raise RuntimeError('the selected proof did not use a clause')
    rejects['wrong_clause_antecedent'] = wrong_antecedent

    # B(y) = D_{r,v}(y=y). The branch really works from B(z), but the
    # primitive compound introduction requires B(0), where its U fails.
    b_at_z = [[-1, -1]]
    b_at_successor = [[[0, -1], [0, -1]]]
    local_z_equality = ['u', 1, 0, ['r', -1]]
    successor_equality = eval_congruence([0, 1], local_z_equality, -1)
    progressive_branch = [
        'e', b_at_successor, ['u', 0, 0, ['r', 0]],
        ['i', b_at_successor, 0, successor_equality]]
    if new.derive(progressive_branch, [([0, 0], b_at_z)], 1) != b_at_successor:
        raise RuntimeError('compound-progress counterexample branch is malformed')
    rejects['compound_progress_is_not_primitive'] = {
        'goal': nested_goal, 'proof': ['i', nested_goal, 0, progressive_branch]}
    for name, data in rejects.items():
        if accepts(new, data):
            raise RuntimeError('accepted invalid example: ' + name)
        results.append({'name': name, 'status': 'rejected'})

    # Exercise the canonical comparison verifier, including its changed neutral.
    comp = ['r', 0, 0, 0]
    canonical_refl = ['x', 1, comp, comp]
    canonical.verify({'goal': [0, 0], 'proof': canonical_refl})
    cgoal = [[0, 0]]
    cproof = ['i', cgoal, 0, ['u', 0, 0, canonical_refl]]
    canonical.verify({'goal': cgoal, 'proof': cproof})
    if accepts(canonical, {'goal': [[0, 0, 1], [0, 0, 1]],
                           'proof': canonical_refl}):
        raise RuntimeError('canonical control accepted a noncanonical goal')

    # All delivered positive and negative examples use the public JSON entrypoint.
    cli_runs = 0
    for optimized in (False, True):
        for name, data in list(translated.items()) + list(rejects.items()):
            command = [sys.executable] + (['-O'] if optimized else [])
            command += [str(ROOT / 'code' / 'clausal_eval.py')]
            run = subprocess.run(command, input=json.dumps(data), text=True,
                                 capture_output=True, check=False)
            expected = name in translated
            if (run.returncode == 0) != expected:
                raise RuntimeError('CLI mismatch: ' + name)
            if run.stdout.strip() != ('ACCEPT' if expected else 'REJECT'):
                raise RuntimeError('unexpected CLI output: ' + name)
            cli_runs += 1

    out = ROOT / 'evidence'
    out.mkdir(exist_ok=True)
    (ROOT / 'examples').mkdir(exist_ok=True)
    for name in ('used_induction_hypothesis', 'capture_avoiding_witness',
                 'zero_source_nested_template', 'nested_compound_binders',
                 'closure_specialization_4'):
        (ROOT / 'examples' / (name + '.json')).write_text(
            json.dumps(translated[name], indent=2) + '\n')
    (ROOT / 'examples' / 'reject_false_iterator_counter.json').write_text(
        json.dumps(rejects['iterator_counter_is_not_successor'], indent=2) + '\n')
    report = {'python': sys.version, 'positive_examples': len(translated),
              'negative_examples': len(rejects), 'public_cli_runs': cli_runs,
              'raw_translation_directions': 2, 'tests': results}
    (out / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    metrics = []
    for name in ('clausal_eval', 'matched_control', 'matched_canonical'):
        path = ROOT / 'code' / (name + '.py')
        raw = path.read_bytes()
        tree = ast.parse(raw.decode())
        tree.body = tree.body[1:]
        code = (ast.unparse(tree) + '\n').encode()
        tokens = sum(t.type not in (tokenize.ENCODING, tokenize.ENDMARKER,
                     tokenize.NEWLINE, tokenize.NL, tokenize.INDENT,
                     tokenize.DEDENT, tokenize.COMMENT)
                     for t in tokenize.generate_tokens(io.StringIO(code.decode()).readline))
        packed = gzip.compress(code, compresslevel=9, mtime=0)
        (ROOT / 'code' / (name + '.normalized.py')).write_bytes(code)
        (ROOT / 'code' / (name + '.normalized.py.gz')).write_bytes(packed)
        metrics.append({'program': name, 'normalized_bytes': len(code),
                        'significant_tokens': tokens,
                        'ast_nodes': sum(1 for _ in ast.walk(tree)),
                        'gzip9_bytes': len(packed),
                        'raw_source_bytes': len(raw),
                        'raw_gzip9_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0))})
    (out / 'metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
    print(json.dumps({'positive': len(translated), 'negative': len(rejects),
                      'cli_runs': cli_runs, 'metrics': metrics}, indent=2))


if __name__ == '__main__':
    main()
