#!/usr/bin/env python3
"""Reproduce matched checker metrics and implementation-equivalence checks.

The arithmetic/proof calculus is inherited unchanged. These checks validate
its new input front end. They do not constitute a proof-assistant verification.
Run from any directory with Python 3.12.14 for the reported size coordinates.
"""
import ast
import gzip
import io
import itertools
import json
import random
import subprocess
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ALPHABET = '0123456789[], -'
DIAGNOSTIC = b'The certificate must use integer/list syntax and have a canonical closed goal'
NAMES = ('native_typed_full.py', 'native_typed_eqd.py')
IGNORED = {tokenize.COMMENT, tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE,
           tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}


def function_ast(path, name):
    return next(node for node in ast.parse(path.read_text()).body
                if isinstance(node, ast.FunctionDef) and node.name == name)


def validator(path):
    node = function_ast(path, 'v')
    namespace = {}
    exec(compile(ast.Module(body=[node], type_ignores=[]), str(path), 'exec'), namespace)
    return namespace['v']


def truth(function, *args):
    try:
        return bool(function(*args))
    except Exception:
        return False


def raw_tree(value):
    return type(value) is int or type(value) is list and all(map(raw_tree, value))


def metrics(path):
    source = path.read_text()
    tree = ast.parse(source)
    normalized = (ast.unparse(tree) + '\n').encode()
    return {
        'path': str(path.relative_to(ROOT)),
        'source_bytes': len(source.encode()),
        'normalized_bytes': len(normalized),
        'significant_tokens': sum(token.type not in IGNORED for token in
                                  tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'gzip9_bytes_mtime0': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'already_normalized': source.encode() == normalized,
    }


def run(path, packet, optimized=False):
    argv = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
    result = subprocess.run(argv, input=packet, capture_output=True)
    accepted = result.returncode == 0 and result.stdout.strip() == b'ACCEPT'
    return accepted, result


def require(condition, details):
    if not condition:
        raise AssertionError(details)


rng = random.Random(20261112)
atoms = [None, True, False, -100, -1, 0, 1, 2, 3, 4, 5, 100, 0.0, -0.0,
         1.0, 1e99, float('inf'), float('-inf'), float('nan'), '', '1', '[]',
         ' -1 ', "'", '"', '\\', '\n', ALPHABET, '\u2603', {}, {'0': 0}]
values = atoms + [[]] + [[a] for a in atoms]
values += [[a, b] for a, b in itertools.product(atoms, repeat=2)]


def random_tree(depth=0, integers_only=False):
    if depth == 5 or rng.random() < .55:
        return rng.randrange(-10, 20) if integers_only else rng.choice(atoms)
    return [random_tree(depth+1, integers_only) for _ in range(rng.randrange(5))]


values += [random_tree() for _ in range(20000)]
for index, value in enumerate(values):
    value = json.loads(json.dumps(value))
    expected = raw_tree(value)
    require((not repr(value).strip(ALPHABET)) == expected,
            ('raw typing', index, value, expected))

scoped = [-5, -1, 0, 1, 2, 3, 4, 5, 6, [], [0], [0, 0], [0, 0, 0], [3, 0], [[0, 0]]]
scoped += [random_tree(integers_only=True) for _ in range(30000)]
depths = (0, 1, 2, 3, 4, 9, 10, 25)
corpus = sorted((ROOT / 'tests').glob('*.json'))
profiles = []
for name in NAMES:
    reference, candidate = ROOT/'reference'/name, ROOT/'code'/name
    require(ast.dump(function_ast(reference, 'c')) == ast.dump(function_ast(candidate, 'c')),
            ('kernel changed', name))
    old, new = validator(reference), validator(candidate)
    for index, value in enumerate(values):
        require(truth(old, value) == raw_tree(value), ('baseline raw mode', name, index))
    for index, value in enumerate(scoped):
        for depth in depths:
            require(truth(old, value, depth+2) == truth(new, value, depth),
                    ('scope mismatch', name, index, value, depth))
    cases = []
    for file in corpus:
        packet = file.read_bytes()
        old_accept, old_run = run(reference, packet)
        new_accept, new_run = run(candidate, packet)
        require(old_accept == new_accept, ('corpus mismatch', name, file.name))
        cases.append({'name': file.name, 'accepts': old_accept})
    positive = next(case['name'] for case in cases if case['accepts'])
    sample = json.loads((ROOT/'tests'/positive).read_text())
    invalid = [True, False, None, 1.0, -0.0, float('nan'), float('inf'), '', '123', {}, {'x': 0}]
    for node in invalid:
        packet = json.dumps([node]+sample).encode()
        for optimized in (False, True):
            for program in (reference, candidate):
                accepted, result = run(program, packet, optimized)
                require(not accepted, ('invalid unused prefix accepted', name, node, optimized))
                if program == candidate:
                    require(DIAGNOSTIC in result.stderr,
                            ('diagnostic changed', name, node, optimized))
    valid_prefixes = [0, -1, [], [1, -2, [3]]]
    for prefix in valid_prefixes:
        packet = json.dumps([prefix]+sample, indent=2).encode()
        for optimized in (False, True):
            a, _ = run(reference, packet, optimized)
            b, _ = run(candidate, packet, optimized)
            require(a == b, ('valid unused prefix mismatch', name, prefix, optimized))
    # JSON's four whitespace characters, including tabs and carriage returns,
    # are normalized by the decoder before repr is examined.
    packet = (' \t\r\n'+json.dumps(sample)+'\r\n\t ').encode()
    require(run(reference, packet)[0] == run(candidate, packet)[0], ('JSON whitespace', name))
    # Integer parsing limits are imposed by the same stdlib JSON parser.
    decimal_limit = sys.get_int_max_str_digits()
    manageable = min(4000, decimal_limit) if decimal_limit else 4000
    original = json.dumps(sample)
    for digits in (100, manageable, (decimal_limit+100 if decimal_limit else 5000)):
        packet = ('['+'1'*digits+','+original[1:]).encode()
        a, _ = run(reference, packet)
        b, _ = run(candidate, packet)
        require(a == b, ('integer digit limit mismatch', name, digits))
    profiles.append({
        'name': name,
        'unchanged_kernel_ast': True,
        'raw_json_values_checked': len(values),
        'scope_comparisons': len(scoped)*len(depths),
        'corpus_count': len(cases),
        'corpus_accept_count': sum(case['accepts'] for case in cases),
        'corpus_reject_count': sum(not case['accepts'] for case in cases),
        'invalid_unused_prefix_type_variants': len(invalid),
        'optimized_mode_checked': True,
        'integer_digit_limit_checked': decimal_limit,
        'cases': cases,
    })

report = {
    'python': sys.version,
    'metrics': [metrics(ROOT/folder/name) for name in NAMES for folder in ('reference','code')],
    'profiles': profiles,
    'equivalence_scope': 'Intended integer/list certificate language and successful executions; excludes resource exhaustion.',
    'error_behavior': 'Existing diagnostic retained verbatim. Null and dictionary type failures formerly raised TypeError; the new front end uses the stated ValueError.',
    'mathematical_claim': 'No new arithmetic axioms, logic rules, kernel, or iPRA interpretation are introduced.',
}
(ROOT/'evidence').mkdir(exist_ok=True)
(ROOT/'evidence/validation.json').write_text(json.dumps(report, indent=2)+'\n')
(ROOT/'evidence/metrics.json').write_text(json.dumps({'python':sys.version,'metrics':report['metrics']},indent=2)+'\n')
print(json.dumps({
    'python':sys.version,
    'metrics':report['metrics'],
    'profiles':[{k:v for k,v in profile.items() if k!='cases'} for profile in profiles],
    'status':'PASS',
},indent=2))
