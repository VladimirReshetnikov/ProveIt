"""Regression checks for the strict, inferred-conclusion CE5 checkers."""
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

import control_three_case as three
import checker as two
from compile_proof import from_legacy, translate, legacy_term, legacy_formula, legacy_proof, eliminate

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / 'reference' / 'upstream' / 'code'))
import clausal_eval as legacy
import matched_control as older
from translate import old_refl, old_sym, old_trans, eval_congruence, translate as old_translate


def certificate(p):
    return {'goal': older.derive(p, [], 0), 'proof': p}


def upstream_cases():
    # The 32 fixtures from raw_clausal/tests/verify.py, pinned in PROVENANCE.
    cases = {}
    terms = [0, [0, 0], [0, [0, 0]], [0, 0, 1],
             [[0, 0], 0, [0, 1]], [0, [0, 0], [1, 0, 2]]]
    for j, t in enumerate(terms):
        cases[f'reflexivity_{j}'] = certificate(old_refl(t))
        cases[f'zero_computation_{j}'] = certificate(['z', t, [0, 1]])
    bodies = [0, 1, [0, 1], [1, 0, 2], [0, 1, [2, 1, [0, 2]]]]
    for j, h in enumerate(bodies):
        cases[f'successor_computation_{j}'] = certificate(['s', 0, 0, h])
        major = ['z', 0, h]
        s, t = older.derive(major, [], 0)
        cases[f'template_congruence_{j}'] = certificate(
            ['x', h, major, old_refl(older.opening(h, s))])
    major = old_sym(['z', 0, 1], [], 0)
    h = [1, 1, [2, 1, [0, 2]]]
    cases['zero_source_nested_template'] = certificate(
        ['x', h, major, old_refl(older.opening(h, 0))])
    matrix = [[1, 0, 1], 0]
    context = [([0, 0], [[-1, 0, 1], 0])]
    hypothesis = ['u', 0, 0, old_refl(0)]
    step = old_trans(['s', -1, 0, 1], hypothesis, context, 1)
    induction = ['i', [matrix], 0, step]
    cases['used_induction_hypothesis'] = certificate(induction)
    for j, t in enumerate(terms):
        target = [[t, 0, 1], 0]
        branch = ['u', 0, t, ['z', 0, 1]]
        cases[f'closure_specialization_{j}'] = certificate(['e', target, induction, branch])
    inner_goal = [[[0, -1], [0, -1]]]
    inner = ['i', inner_goal, [0, 0], old_refl([0, -1])]
    cases['nested_compound_binders'] = certificate(['i', [[[3, 3]]], 0, inner])
    witness = [[0, 0], 0, [0, 1]]
    cases['capture_avoiding_witness'] = certificate(
        ['i', [[[1, 2, 3], 2]], witness, ['s', -1, witness, witness]])
    return {name: old_translate(data) for name, data in cases.items()}


def accepts(checker, data):
    try:
        checker.verify(data)
        return True
    except Exception:
        return False


def nodes(p):
    tag = p[0]
    if tag == 'r':
        return 1
    if tag in ('u', 'i'):
        return 1 + nodes(p[3])
    return 1 + nodes(p[1]) + nodes(p[2])


def substitution_checks():
    rng = random.Random(3512)
    def term(scope, depth, fuel):
        if not fuel or rng.randrange(3) == 0:
            return rng.choice(list(range(-scope, depth + 1)))
        if rng.randrange(2):
            return [0, term(scope, depth, fuel - 1)]
        return [term(scope, depth, fuel - 1), term(scope, depth, fuel - 1),
                term(scope, depth + 1, fuel - 1)]
    def formula(scope, depth, fuel):
        if fuel and rng.randrange(2):
            return [formula(scope, depth + 2, fuel - 1)]
        return [term(scope, depth, fuel), term(scope, depth, fuel)]
    for _ in range(500):
        scope = rng.randrange(4)
        value = term(scope, 0, 3)
        a = term(scope, 1, 3)
        assert two.opening(legacy_term(a), legacy_term(value)) == legacy_term(legacy.opening(a, value))
        f = formula(scope, 2, 3)
        assert two.opening(legacy_formula(f), legacy_term(value), 1) == legacy_formula(legacy.opening(f, value, 1))
    return 1000


def main():
    old_cases = upstream_cases()
    positive = {name: translate(from_legacy(data)) for name, data in old_cases.items()}
    for name, data in old_cases.items():
        legacy.verify(data)
        tagged = from_legacy(data)
        two.verify(positive[name])
        assert nodes(positive[name]['proof']) <= 3 * nodes(tagged['proof'])
    z = ['z']
    one = ['s', z]
    truth = ['=', z, z]
    refl = ['r', z]
    base = {'goal': truth, 'proof': refl}
    rejects = {
        'extra_field': dict(base, extra=0),
        'zero_variable': {'goal': ['=', ['v', 0], ['v', 0]], 'proof': ['r', ['v', 0]]},
        'boolean_variable': {'goal': truth, 'proof': ['r', ['v', True]]},
        'float_variable': {'goal': truth, 'proof': ['r', ['v', 1.0]]},
        'free_variable': {'goal': ['=', ['v', -1], ['v', -1]], 'proof': ['r', ['v', -1]]},
        'loose_bound_variable': {'goal': ['=', ['v', 1], ['v', 1]], 'proof': ['r', ['v', 1]]},
        'unknown_rule': {'goal': truth, 'proof': ['unknown', z]},
        'extra_rule_argument': {'goal': truth, 'proof': ['r', z, z]},
        'forged_goal': {'goal': ['=', z, one], 'proof': refl},
        'nonexistent_clause': {'goal': truth, 'proof': ['u', 0, z, refl]},
        'negative_clause': {'goal': truth, 'proof': ['u', -1, z, refl]},
        'boolean_clause': {'goal': truth, 'proof': ['u', False, z, refl]},
        'formula_as_term': {'goal': truth, 'proof': ['r', truth]},
        'bad_iterator_arity': {'goal': truth, 'proof': ['r', ['i', z, z]]},
        'bad_successor_arity': {'goal': truth, 'proof': ['r', ['s', z, z]]},
        'bad_binder_arity': {'goal': ['d', truth, truth], 'proof': refl},
        'zero_eval_wrong_source': {'goal': truth,
            'proof': ['v', ['r', one], ['r', ['i', z, z, ['v', 1]]]]},
        'successor_as_iterator': {'goal': truth, 'proof': ['v', refl, ['r', one]]},
        'wrong_successor_source': {'goal': truth,
            'proof': ['v', refl, ['r', ['i', one, z, ['v', 1]]]]},
        'witness_escape': {'goal': ['d', truth], 'proof': ['i', truth, ['v', -1], refl]},
        'direct_identity_deleted': {'goal': truth, 'proof': ['v', refl, refl]},
    }
    induction = positive['used_induction_hypothesis']['proof']
    rejects['compound_eval_major'] = {'goal': truth, 'proof': ['v', induction, refl]}
    rejects['compound_eval_minor'] = {'goal': truth, 'proof': ['v', refl, induction]}
    rejects['eigenvariable_escape'] = {'goal': truth,
        'proof': ['e', induction, ['r', ['v', -1]]]}
    rejects['fresh_out_of_scope'] = {'goal': truth,
        'proof': ['e', induction, ['r', ['v', -2]]]}
    raw_bad = json.loads((ROOT.parent / 'reference/upstream/examples/reject_false_iterator_counter.json').read_text())
    rejects['iterator_counter_is_not_successor'] = {
        'goal': legacy_formula(raw_bad['goal']), 'proof': legacy_proof(raw_bad['proof'])}
    def change_clause_premise(p):
        if type(p) is list:
            if p and p[0] == 'u':
                p[3] = ['r', one]
                return True
            return any(change_clause_premise(x) for x in p)
        return False
    wrong_base = copy.deepcopy(positive['used_induction_hypothesis'])
    assert change_clause_premise(wrong_base['proof'])
    rejects['wrong_clause_antecedent'] = wrong_base
    cases_mode = copy.deepcopy(positive['used_induction_hypothesis'])
    cases_mode['proof'][2] = one
    rejects['progress_retagged_as_cases'] = cases_mode
    # Compile a step valid under B(z), then try to use it where compound DI
    # requires B(0). The theorem can be true although this proof is invalid.
    bz = [[-1, -1]]
    bs = [[[0, -1], [0, -1]]]
    equality = ['u', 1, 0, ['r', -1]]
    step_equality = eval_congruence([0, 1], equality, -1)
    step = ['e', bs, ['u', 0, 0, ['r', 0]], ['i', bs, 0, step_equality]]
    context = [(['=', z, z], legacy_formula(bz))]
    branch = eliminate(legacy_proof(step), context, 1)
    nested = legacy_formula([[[3, 3]]])
    rejects['compound_progress_is_not_primitive'] = {
        'goal': nested, 'proof': ['i', nested[1], z, branch]}
    for name, data in rejects.items():
        assert not accepts(two, data), name
    assert accepts(three, rejects['direct_identity_deleted'])
    two.verify(translate(rejects['direct_identity_deleted']))
    # The inferred-elimination rule checks its conclusion at the parent scope.
    # A branch may use the fresh variable internally; it may not return it.
    cli_runs = 0
    for optimized in (False, True):
        for name, data in list(positive.items()) + list(rejects.items()):
            command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / 'checker.py')]
            run = subprocess.run(command, input=json.dumps(data), text=True, capture_output=True)
            expected = name in positive
            assert (run.returncode == 0) == expected, name
            assert run.stdout.strip() == ('ACCEPT' if expected else 'REJECT'), name
            cli_runs += 1
    substitutions = substitution_checks()
    metrics = []
    for path in (ROOT / 'checker.py', ROOT / 'control_three_case.py', ROOT.parent / 'reference/upstream/code/clausal_eval.py'):
        name = path.name
        tree = ast.parse(path.read_text())
        if isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant):
            tree.body.pop(0)
        code = (ast.unparse(tree) + '\n').encode()
        tokens = sum(t.type not in (tokenize.ENCODING, tokenize.ENDMARKER,
            tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT)
            for t in tokenize.generate_tokens(io.StringIO(code.decode()).readline))
        metrics.append({'program': name, 'normalized_bytes': len(code),
            'significant_tokens': tokens, 'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'gzip9_bytes': len(gzip.compress(code, compresslevel=9, mtime=0))})
        path.with_suffix('.normalized.py').write_bytes(code)
        path.with_suffix('.normalized.py.gz').write_bytes(gzip.compress(code, compresslevel=9, mtime=0))
    report = {'positive_examples': len(positive), 'negative_examples': len(rejects),
        'public_cli_runs': cli_runs, 'substitution_comparisons': substitutions,
        'proof_node_bound': 'translated <= 3 * source', 'metrics': metrics,
        'positive_names': list(positive), 'negative_names': list(rejects)}
    (ROOT.parent / 'evidence/readable_validation.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
