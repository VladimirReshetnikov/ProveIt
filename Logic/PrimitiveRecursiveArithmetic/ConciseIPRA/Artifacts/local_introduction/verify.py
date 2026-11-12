"""Untrusted compiler, standalone kernels, and malformed-input checks."""
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'code'))
import diagonal_control as C
import diagonal_newest as N
from compile_newest import (translate, compile_proof, clause_realizer,
                            reflexivity, hypothesis, symmetry, transport, diagonal)


def S(x):
    return [0, x]


def checked(goal, proof):
    data = {'goal': goal, 'proof': proof}
    C.verify(data)
    return data


def close(goal, witness, branch, context=(), scope=0):
    fresh = -scope - 1
    matrix = goal[0]
    body = C.opening(matrix, witness, 2)
    eta = fresh if diagonal(matrix) else 0
    local = list(context) + [([], C.opening(body, eta))]
    result = ['i', goal, witness, branch(local, scope + 1)]
    C.derive(result, list(context), scope)
    return result


def measure(path):
    source = ast.unparse(ast.parse(path.read_text())) + '\n'
    skip = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
            tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT}
    return {'significant_tokens': sum(t.type not in skip for t in
            tokenize.generate_tokens(io.StringIO(source).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(source))),
            'normalized_utf8_bytes': len(source.encode()),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def main():
    cases = {}
    cases['alias_reflexivity_zero'] = checked([0, 0], reflexivity(0)([], 0))
    term = [0, S(0), 1]
    cases['alias_reflexivity_iterator'] = checked([term, term], reflexivity(term)([], 0))
    cases['zero_computation'] = checked([[0, S(0), 1], S(0)], ['c', 0, S(0), 1])
    cases['successor_computation'] = checked([[S(0), 0, S(1)], S([0, 0, S(1)])],
                                            ['c', S(0), 0, S(1)])
    cases['nested_alias_dependency'] = checked([S(0), S(0)],
        ['a', 0, ['a', S(-1), ['u', 1, None]]])
    s = [0, 0, 1]
    eq = lambda context, scope: ['c', 0, 0, 1]
    cases['derived_symmetry'] = checked([0, s], symmetry(eq, C)([], 0))
    F = lambda v: [S(v), S(0)]
    cases['derived_zero_source_transport'] = checked(F(s),
        transport(F, symmetry(eq, C), reflexivity(S(0)), C)([], 0))

    name = [[[1, 0, 3], [1, 0, S(0)]]]
    cases['nonzero_close_witness'] = checked(name,
        close(name, S(0), lambda context, scope:
              reflexivity([S(-scope), 0, S(0)])(context, scope)))

    diag = [[[1, 1, 1], [1, 1, 1]]]
    def diag_branch(context, scope):
        conclusion = C.opening(C.opening(diag[0], S(0), 2), S(-scope))
        return transport(lambda unused: conclusion,
                         hypothesis(len(context) - 1),
                         reflexivity(conclusion[0]), C)(context, scope)
    cases['diagonal_progress_hypothesis_consumed'] = checked(diag,
        close(diag, S(0), diag_branch))

    witness_diag = [[[1, 1, 3], [1, 1, [0, 3, 0]]]]
    def witness_diag_branch(context, scope):
        counter = S(-scope)
        witness = S(0)
        left = [counter, counter, witness]
        right = [counter, counter, [0, witness, 0]]
        cleft = lambda ctx, sc: ['c', counter, counter, witness]
        cright = lambda ctx, sc: ['c', counter, counter, [0, witness, 0]]
        czero = lambda ctx, sc: ['c', 0, witness, 0]
        right_to_witness = transport(lambda value: [right, value], czero, cright, C)
        step_equality = transport(lambda value: [value, right], symmetry(cleft, C),
                                 symmetry(right_to_witness, C), C)
        return transport(lambda unused: [left, right], hypothesis(len(context) - 1),
                         step_equality, C)(context, scope)
    cases['diagonal_progress_with_nonzero_witness'] = checked(witness_diag,
        close(witness_diag, S(0), witness_diag_branch))

    constant = [[0, 0]]
    cases['case_close_equation'] = checked(constant,
        close(constant, S(S(0)), lambda context, scope: ['u', len(context) - 1, None]))
    nested = [constant]
    cases['case_close_compound'] = checked(nested,
        close(nested, S(0), lambda context, scope: ['u', len(context) - 1, None]))

    formula = lambda v: [[v, 0]]
    def source_compound(context, scope):
        return close(formula(s), 0, lambda ctx, sc: ['c', 0, 0, 1], context, scope)
    cases['transport_beneath_D'] = checked(formula(0),
        transport(formula, eq, source_compound, C)([], 0))

    source_major = cases['case_close_equation']['proof']
    cases['open_and_use_conditional_clause'] = checked([0, 0],
        ['e', [0, 0], source_major, ['u', 0, reflexivity(0)([([0, 0], [0, 0])], 1)]])

    for number in range(1, 5):
        n = 0
        for unused in range(number):
            n = S(n)
        term = [0, n, 1]
        major = lambda context, scope, n=n: ['c', 0, n, 1]
        template = lambda v, term=term: [[0, v, term], [0, term, term]]
        cases[f'passive_source_{number}'] = checked(template(n),
            transport(template, major, reflexivity([0, term, term]), C)([], 0))

    results = []
    for name, source in cases.items():
        target = translate(source)
        for kind, data in [('control', source), ('newest', target)]:
            path = ROOT / 'tests' / kind / (name + '.json')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(data, separators=(',', ':')) + '\n')
            program = ROOT / 'code' / ('diagonal_control.py' if kind == 'control' else 'diagonal_newest.py')
            for optimized in (False, True):
                command = [sys.executable, '-I', '-S'] + (['-O'] if optimized else []) + [str(program)]
                run = subprocess.run(command, input=json.dumps(data), text=True, capture_output=True, timeout=30)
                accepted = run.returncode == 0 and run.stdout == 'ACCEPT\n'
                if not accepted:
                    raise AssertionError((name, kind, optimized, run.stderr))
                results.append({'case': name, 'program': kind, 'optimized': optimized,
                                'expected': True, 'accepted': accepted})

    attacks = {
        'fresh_alias_capture': {'goal': [0, 0], 'proof': ['a', -1, ['u', 0, None]]},
        'bound_alias_capture': {'goal': [0, 0], 'proof': ['a', 1, ['u', 0, None]]},
        'boolean_alias': {'goal': [0, 0], 'proof': ['a', False, ['u', 0, None]]},
        'float_alias': {'goal': [0, 0], 'proof': ['a', 0.0, ['u', 0, None]]},
        'future_parameter_in_computation': {'goal': [0, 0], 'proof': ['c', 0, -1, 1]},
        'erased_bad_body': {'goal': [0, 0], 'proof': ['c', 0, 0, -1]},
        'wrong_counter_constructor': {'goal': [0, 0], 'proof': ['c', [0, 0, 0], 0, 1]},
        'back_zero_source': {'goal': [0, 0], 'proof': ['v', [0, 0], ['a', 0, ['u', 0, None]], ['a', 0, ['u', 0, None]]]},
        'old_back_source': {'goal': [0, 0], 'proof': ['a', 0, ['a', 0, ['v', [-1, 0], ['u', 0, None], ['a', 0, ['u', 2, None]]]]]},
        'unproved_false': {'goal': [0, S(0)], 'proof': ['a', 0, ['u', 0, None]]},
        'negative_clause_index': {'goal': [0, 0], 'proof': ['a', 0, ['u', -1, None]]},
        'boolean_clause_index': {'goal': [0, 0], 'proof': ['a', 0, ['u', False, None]]},
        'unknown_rule': {'goal': [0, 0], 'proof': ['unknown']},
        'boolean_public_goal': {'goal': [False, False], 'proof': ['a', 0, ['u', 0, None]]},
        'free_public_goal': {'goal': [-1, -1], 'proof': ['a', 0, ['u', 0, None]]},
        'extra_close_witness': {'goal': constant, 'proof': ['i', constant, 0, ['u', 0, None]]},
        'equation_as_close_goal': {'goal': [0, 0], 'proof': ['i', [0, 0], ['u', 0, None]]},
        'open_equation_major': {'goal': [0, 0], 'proof': ['e', [0, 0], ['a', 0, ['u', 0, None]], ['u', 0, None]]},
    }
    for name, data in attacks.items():
        path = ROOT / 'tests' / 'adversarial' / (name + '.json')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(data, separators=(',', ':')) + '\n')
        for optimized in (False, True):
            command = [sys.executable, '-I', '-S'] + (['-O'] if optimized else []) + [str(ROOT / 'code/diagonal_newest.py')]
            run = subprocess.run(command, input=json.dumps(data), text=True, capture_output=True, timeout=30)
            accepted = run.returncode == 0 and run.stdout == 'ACCEPT\n'
            if accepted:
                raise AssertionError(('attack accepted', name, optimized))
            results.append({'case': name, 'program': 'newest', 'optimized': optimized,
                            'expected': False, 'accepted': accepted})

    sc = [([], [-1, 0]), ([], [0, 0])]
    source_proof = ['v', [-1, -1], ['u', 0, None], ['u', 1, None]]
    tc = [([], [0, 0]), ([], [-3, 0]), ([], [-4, -4]), ([], [0, 0])]
    embedded = compile_proof(source_proof, sc, 1, tc, 4, {-1: -3},
                             [clause_realizer(1), clause_realizer(3)])
    if N.derive(embedded, tc, 4) != [-3, -3]:
        raise AssertionError('arbitrary embedding')
    result = {'python': sys.version, 'source_cases': len(cases),
              'adversarial_cases': len(attacks), 'process_runs': len(results),
              'failed_checks': 0, 'non_order_preserving_embedding': True,
              'metrics': {name: measure(ROOT / 'code' / (name + '.py'))
                          for name in ['diagonal_control', 'diagonal_newest']},
              'results': results,
              'limits': ['Finite tests supplement the written general compiler proof.',
                         'No Lean or Rocq formalization of the new equivalence is claimed.',
                         'Progress fixtures consume the induction hypothesis; no claim is made that their theorems require induction.']}
    (ROOT / 'evidence/validation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'results'}, indent=2))


if __name__ == '__main__':
    main()
