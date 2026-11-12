"""Reproduce certificate, adversarial, control, fuel and CLI checks."""
from pathlib import Path
import ast
import copy
import gzip
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize

import checker
import checker_fuel
import control
import control_fuel
import proof_tools as p
from build_examples import examples

HERE = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def rejected(module, data):
    try:
        module.check(data)
    except Exception:
        return True
    return False


def metrics(path):
    source = Path(path).read_bytes()
    tree = ast.parse(source)
    if (tree.body and isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and isinstance(tree.body[0].value.value, str)):
        tree.body.pop(0)
    normalized = (ast.unparse(tree) + '\n').encode()
    omitted = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(t.type not in omitted for t in tokenize.generate_tokens(
        io.StringIO(normalized.decode()).readline))
    return {'normalized_bytes': len(normalized), 'significant_tokens': tokens,
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'gzip9_bytes': len(gzip.compress(normalized, 9, mtime=0)),
            'raw_bytes': len(source), 'sha256': hashlib.sha256(source).hexdigest()}


def negatives(positive):
    out = {}
    def put(name, goal, proof):
        out[name] = {'goal': goal, 'proof': proof}
    r = p.refl(0)
    put('false_equation', [0, p.ONE], r)
    put('boolean_goal_alias', [False, False], r)
    put('float_goal_alias', [0.0, 0.0], r)
    put('unbound_goal', [1, 1], r)
    put('free_goal', [-1, -1], r)
    put('empty_goal', [], r)
    put('string_goal', '[0, 0]', r)
    put('unknown_instruction', [0, 0], ['x'])
    put('wrong_instruction_arity', [0, 0], ['u', 0, 0])
    put('extra_instruction_field', [0, 0], ['u', 0, 0, None, 0])
    put('negative_clause', [0, 0], ['u', -1, 0, None])
    put('boolean_clause', [0, 0], ['u', False, 0, None])
    put('missing_clause', [0, 0], ['u', 1, 0, None])
    for name, term in [('boolean_term', False), ('float_term', 0.0),
                       ('unbound_term', 1), ('free_term', -1),
                       ('invalid_successor', [1, 0]), ('empty_term', []),
                       ('zero_redex', [0, 0, 1]),
                       ('successor_redex', [p.ONE, 0, 1]),
                       ('erased_malformed_update', [0, 0, 99]),
                       ('boolean_successor', [False, 0])]:
        put(name, [0, 0], ['u', 0, term, None])
    put('malformed_intro_matrix', [[3, 3]], ['i', [3, 3], 0, r])
    put('erased_invalid_intro_matrix', [[[0, 0, 99], 0]],
        ['i', [[0, 0, 99], 0], 0, r])
    put('intro_free_witness', [[0, 0]], ['i', [0, 0], -1, r])
    put('intro_boolean_witness', [[0, 0]], ['i', [0, 0], False, r])
    put('equation_as_elimination_major', [0, 0], ['e', r, r])
    ordinary = positive['ordinary_elimination_fallback']['proof'][1]
    put('eigenvariable_escape', [-1, -1], ['e', ordinary, p.refl(-1)])
    put('hidden_eigenvariable_escape', [0, 0], ['e', ordinary, p.refl(-1)])
    put('branch_clause_used_in_major', [0, 0], ['e', p.use(1, 0), r])
    # The matrix denotes (0=1 -> 0=1), so its D-introduction is valid.
    # Its conditional clause cannot be used with a reflexivity premise.
    false_matrix = [0, p.ONE]
    major = ['i', false_matrix, p.ONE, p.use(1, 0)]
    put('wrong_clause_antecedent', [0, p.ONE], ['e', major, p.use(1, 0, r)])
    name = positive['branch_uses_specialized_clause']['proof']
    put('old_unspecialized_branch_goal', [-1, p.ONE], copy.deepcopy(name))
    out['extra_document_field'] = {'goal': [0, 0], 'proof': r, 'extra': 1}
    out['missing_goal'] = {'proof': r}
    out['missing_proof'] = {'goal': [0, 0]}
    out['array_document'] = []
    out['null_document'] = None
    return out


def guard_creation_check():
    """Open-sequent regression for the nontrivial substitution lemma."""
    parameter = -1
    raw = [p.C(p.Y, 0, p.C(parameter, p.X, 0)), p.C(p.Y, 0, p.ONE)]
    D = p.D(raw)
    context = p.INITIAL + [([], D)]
    proof = ['e', p.use(1, 0), ['i', D[0], -2, p.use(2, p.ONE, p.refl(0))]]
    require(checker.prove(proof, context) == D, 'open eta proof failed')
    def substitute_syntax(a):
        return p.at(a, parameter, 0)
    D0 = substitute_syntax(D)
    changed_context = p.INITIAL + [([], D0)]
    naive = ['e', p.use(1, 0), ['i', D0[0], -2, p.use(2, p.ONE, p.refl(0))]]
    try:
        checker.prove(naive, changed_context)
    except Exception:
        pass
    else:
        raise AssertionError('guard-creation naive proof unexpectedly accepted')
    repaired = ['e', p.use(1, 0), ['i', D0[0], p.ONE, p.use(2, p.ONE, p.refl(0))]]
    require(checker.prove(repaired, changed_context) == D0, 'guard repair failed')
    return {'original': {'context': context, 'proof': proof, 'goal': D},
            'naive_substitution': {'context': changed_context, 'proof': naive,
                                   'goal': D0, 'accepted': False},
            'repaired_substitution': {'context': changed_context, 'proof': repaired,
                                      'goal': D0, 'accepted': True}}


def main():
    positive = examples()
    negative = negatives(positive)
    example_dir = HERE / 'examples'
    reject_dir = HERE / 'reject_examples'
    control_dir = HERE / 'control_examples'
    fuel_dir = HERE / 'fuel_examples'
    for directory in [example_dir, reject_dir, control_dir, fuel_dir]:
        directory.mkdir(exist_ok=True)
    fuel_costs = {}
    for name, data in positive.items():
        checker.check(data)
        controlled = {'goal': data['goal'], 'proof': p.to_control(data['proof'])}
        control.check(controlled)
        fuelled = dict(data, fuel=2000000)
        checker_fuel.check(fuelled)
        spent = fuelled['fuel'] - checker_fuel.remaining
        exact = dict(data, fuel=spent)
        checker_fuel.check(exact)
        require(checker_fuel.remaining == 0, 'exact fuel mismatch')
        require(rejected(checker_fuel, dict(data, fuel=spent - 1)), 'underfuel accepted')
        control_fuel.check(dict(controlled, fuel=2000000))
        fuel_costs[name] = spent
        (example_dir / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
        (control_dir / (name + '.json')).write_text(json.dumps(controlled, indent=2) + '\n')
        (fuel_dir / (name + '.json')).write_text(json.dumps(exact, indent=2) + '\n')
    for name, data in negative.items():
        require(rejected(checker, data), 'invalid certificate accepted: ' + name)
        (reject_dir / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    for fuel in [-1, False, 1.5, '100', None, 0]:
        require(rejected(checker_fuel, dict(positive['reflexivity'], fuel=fuel)),
                'bad fuel accepted')
    cli_checks = 0
    for optimized in [False, True]:
        command = [sys.executable] + (['-O'] if optimized else []) + [str(HERE / 'checker.py')]
        for accepted, group in [(True, positive), (False, negative)]:
            for name, data in group.items():
                result = subprocess.run(command, input=json.dumps(data), text=True,
                                        capture_output=True, timeout=30)
                require((result.returncode == 0) == accepted, 'CLI status ' + name)
                require((result.stdout.strip() == 'ACCEPT') == accepted, 'CLI output ' + name)
                cli_checks += 1
        for text in ['', '{', 'null', 'true', '0', '"certificate"',
                     '{"goal":NaN,"proof":[]}']:
            result = subprocess.run(command, input=text, text=True,
                                    capture_output=True, timeout=30)
            require(result.returncode != 0 and 'ACCEPT' not in result.stdout,
                    'malformed JSON accepted')
            cli_checks += 1
    guard = guard_creation_check()
    (HERE / 'guard_creation.json').write_text(json.dumps(guard, indent=2) + '\n')
    selected = ['checker.py', 'control.py', 'checker_fuel.py', 'control_fuel.py',
                'output_checker.py', 'output_control.py']
    measurement = {name: metrics(HERE / name) for name in selected}
    evidence = {'python': platform.python_version(),
                'accepted': sorted(positive), 'rejected': sorted(negative),
                'cli_checks': cli_checks, 'control_translations': len(positive),
                'fuel_exact_and_one_less_checks': 2 * len(positive),
                'fuel_costs': fuel_costs, 'guard_creation_regression': True,
                'metrics': measurement}
    (HERE / 'verification.json').write_text(json.dumps(evidence, indent=2) + '\n')
    (HERE / 'metrics.json').write_text(json.dumps(measurement, indent=2) + '\n')
    print(json.dumps(evidence, indent=2))


if __name__ == '__main__':
    main()
