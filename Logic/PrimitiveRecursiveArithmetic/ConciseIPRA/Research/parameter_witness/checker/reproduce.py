"""Reproduce finite checks and complete-module size measurements.

This is an untrusted driver. checker.py imports no part of this script.
"""
from pathlib import Path
import ast
import copy
import hashlib
import importlib.util
import io
import json
import platform
import subprocess
import sys
import tokenize

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parent

def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result

NEW = module('newest_checker', ROOT / 'checker.py')
OLD = module('old_checker', ROOT / 'reference/raw_three_case.py')
S = lambda t: [0, t]
I = lambda n, a, h: [n, a, h]
R = lambda t: ['r', t]


def compile_selected(proof, context=(), scope=0):
    """Convert the selected corpus, not a universal witness compiler.

    Root equality is removed by the inherited two-case framing construction.
    Only introductions already at zero or the newest parameter are handled.
    """
    tag = proof[0]
    if tag == 'r':
        return copy.deepcopy(proof)
    if tag == 'u':
        return ['u', proof[1], copy.deepcopy(proof[2]),
                compile_selected(proof[3], context, scope)]
    if tag == 'v':
        s, t = OLD.derive(proof[1], list(context), scope)
        b, r = OLD.derive(proof[2], list(context), scope)
        first = compile_selected(proof[1], context, scope)
        second = compile_selected(proof[2], context, scope)
        if b == s:
            return ['v', first, ['v', second, ['r', [0, s, 0]]]]
        return ['v', first, second]
    goal, data, branch = proof[1:]
    fresh = -scope - 1
    if tag == 'e':
        paired = OLD.derive(data, list(context), scope)
        body = OLD.opening(paired[0], fresh, 1)
        clause = (OLD.opening(body, 0), body)
        data = compile_selected(data, context, scope)
    else:
        if type(data) is not int or data not in (0, -scope):
            raise ValueError('selected compiler requires an existing atomic witness')
        body = OLD.opening(goal[0], data, 1)
        eta = fresh if len(goal[0]) == 2 and data == 0 else 0
        clause = ([0, 0], OLD.opening(body, eta))
        data = int(data != 0)
    return [tag, copy.deepcopy(goal), data,
            compile_selected(branch, context + (clause,), scope + 1)]


def measure(path):
    source = path.read_bytes()
    tree = ast.parse(source.decode())
    if (tree.body and isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and isinstance(tree.body[0].value.value, str)):
        tree.body.pop(0)
    normalized = (ast.unparse(tree) + '\n').encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NL,
               tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
               tokenize.COMMENT}
    tokens = tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
    return {
        'path': str(path.relative_to(ROOT)),
        'source_sha256': hashlib.sha256(source).hexdigest(),
        'git_blob_sha1': hashlib.sha1(b'blob ' + str(len(source)).encode()
                                    + b'\0' + source).hexdigest(),
        'normalized_bytes': len(normalized),
        'significant_tokens': sum(t.type not in ignored for t in tokens),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
    }


def main():
    from generate_examples import main as generate
    generate()
    truth = [[0, 0]]
    truth_proof = ['i', truth, 0, R(0)]
    xx = [[2, 2]]
    cases = {
        'zero_progress': ({'goal': truth, 'proof': truth_proof}, True),
        'newest_case': ({'goal': xx,
                         'proof': ['e', xx, truth_proof,
                                   ['i', xx, 1, R(-1)]]}, True),
        'newest_case_two_parameters': ({'goal': xx,
            'proof': ['e', xx, truth_proof,
                      ['e', xx, truth_proof, ['i', xx, 1, R(-2)]]]}, True),
        'reject_older_parameter_as_newest': ({'goal': xx,
            'proof': ['e', xx, truth_proof,
                      ['e', xx, truth_proof, ['i', xx, 1, R(-1)]]]}, False),
        'empty_scope_case_mode': ({'goal': truth,
                                  'proof': ['i', truth, 1, R(0)]}, True),
        'reject_old_term_witness_payload': ({'goal': xx,
                    'proof': ['i', xx, S(0), R(S(0))]}, False),
        'reject_bound_index_capture': ({'goal': xx,
                    'proof': ['i', xx, 1, R(1)]}, False),
        'reject_unallocated_parameter': ({'goal': xx,
                    'proof': ['i', xx, 1, R(-2)]}, False),
        'reject_bad_goal_arity': ({'goal': [0, 0, 0],
                                  'proof': R(0)}, False),
        'reject_boolean_arithmetic': ({'goal': [False, False],
                                       'proof': R(False)}, False),
        'reject_float_arithmetic': ({'goal': [0.0, 0.0],
                                     'proof': R(0.0)}, False),
        'reject_nan_arithmetic': ({'goal': [float('nan'), 0],
                                   'proof': R(0)}, False),
        'reject_free_public_goal': ({'goal': [-1, -1],
                                    'proof': R(-1)}, False),
        'reject_unknown_tag': ({'goal': [0, 0],
                               'proof': ['assume', [0, 0]]}, False),
        'reject_missing_branch': ({'goal': truth,
                                   'proof': ['i', truth, 0]}, False),
        'reject_wrong_formula': ({'goal': [0, S(0)],
                                  'proof': R(0)}, False),
    }
    # FALSE in N: exists x forall y [C(y,0,Sx)=y].  A leaked induction
    # eigenparameter would make the successor rows reflexive.
    false_goal = [[I(1, 0, S(3)), 1]]
    previous = I(-1, 0, S(-1))
    following = I(S(-1), 0, S(-1))
    cases['reject_eigenparameter_escape'] = ({
        'goal': false_goal,
        'proof': ['i', false_goal, 1, ['v', R(previous), R(following)]]}, False)

    # Noncanonical mode payloads are explicitly decoded by truthiness.
    # They are bit aliases, never terms or programs.
    aliases = [('false_null', None, False), ('false_empty_list', [], False),
               ('false_empty_object', {}, False), ('false_empty_text', '', False),
               ('true_negative_int', -7, True), ('true_object', {'a': 1}, True),
               ('true_text', 'mode-one', True), ('true_nan', float('nan'), True)]
    for name, value, bit in aliases:
        if bit:
            payload = {'goal': xx, 'proof': ['e', xx, truth_proof,
                                           ['i', xx, value, R(-1)]]}
        else:
            payload = {'goal': truth, 'proof': ['i', truth, value, R(0)]}
        cases['mode_alias_' + name] = (payload, True)

    for path in sorted((ROOT / 'fixtures/generated').glob('*.json')):
        cases[path.stem] = (json.loads(path.read_text()), True)
    for path in sorted((ROOT / 'fixtures/inherited').glob('*.json')):
        original = json.loads(path.read_text())
        OLD.verify(original)
        converted = {'goal': original['goal'],
                     'proof': compile_selected(original['proof'])}
        cases['inherited_' + path.stem] = (converted, True)

    # Mutate substantive packet outputs at the two checked boundaries.
    packet = copy.deepcopy(cases['packet_closure'][0])
    packet['goal'] = [[0, S(0)]]
    cases['reject_packet_changed_goal'] = (packet, False)
    packet = copy.deepcopy(cases['packet_closure'][0])
    packet['proof'][2] = 1  # dummy witness is absent: harmless bit change
    cases['packet_unused_dummy_mode_one'] = (packet, True)
    packet = copy.deepcopy(cases['packet_closure'][0])
    packet['proof'][3][2] = 0  # inner witness must be n, not zero
    cases['reject_packet_wrong_inner_mode'] = (packet, False)
    packet = copy.deepcopy(cases['packet_closure'][0])
    packet['proof'][3][1] = [[0, S(0)]]
    cases['reject_packet_changed_inner_matrix'] = (packet, False)

    receipts = []
    destination = ROOT / 'fixtures/checked'
    destination.mkdir(parents=True, exist_ok=True)
    for name, (payload, expected) in cases.items():
        encoded = json.dumps(payload, indent=2) + '\n'
        (destination / (name + '.json')).write_text(encoded)
        runs = []
        for optimized in (False, True):
            command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / 'checker.py')]
            run = subprocess.run(command, input=encoded, text=True,
                                 capture_output=True, timeout=10)
            accepted = run.returncode == 0 and run.stdout == 'ACCEPT\n'
            if accepted != expected:
                raise AssertionError((name, optimized, expected, run.returncode,
                                      run.stdout, run.stderr))
            runs.append({'optimized_python': optimized,
                         'exit_code': run.returncode, 'accepted': accepted})
        receipts.append({'fixture': name, 'expected_accept': expected, 'runs': runs})

    metrics = {'python': platform.python_version(),
               'method': 'Remove only module docstring; ast.unparse; append LF; count whole module.',
               'programs': {name: measure(ROOT / path) for name, path in {
                   'pinned_three_case': 'reference/raw_three_case.py',
                   'pinned_two_case': 'reference/raw_two_case.py',
                   'newest_bit': 'checker.py'}.items()}}
    validation = {'python': platform.python_version(),
                  'distinct_fixtures': len(receipts),
                  'process_runs': 2 * len(receipts),
                  'accepting_fixtures': sum(row['expected_accept'] for row in receipts),
                  'rejecting_fixtures': sum(not row['expected_accept'] for row in receipts),
                  'mismatches': 0,
                  'claim': 'Finite implementation checks, not formal verification or exhaustive proof search.',
                  'receipts': receipts}
    (ROOT / 'METRICS.json').write_text(json.dumps(metrics, indent=2) + '\n')
    (ROOT / 'VALIDATION.json').write_text(json.dumps(validation, indent=2) + '\n')
    print(json.dumps({'metrics': metrics,
                      'validation': {k: v for k, v in validation.items() if k != 'receipts'}}, indent=2))

if __name__ == '__main__':
    main()
