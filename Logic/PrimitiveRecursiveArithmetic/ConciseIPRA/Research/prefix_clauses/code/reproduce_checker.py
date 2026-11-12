"""Reproduce the counted-prefix checker comparisons and finite validation.

Tests do not prove the metatheorems. Positive certificates are translated to
both the matched nested calculus and the independently retrieved upstream
uniform-clause checker, which are then run as separate processes.
"""
from __future__ import annotations

import ast
import copy
import gzip
import hashlib
import importlib.util
import io
import json
import platform
import random
import subprocess
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'evidence'
EXAMPLES = ROOT / 'examples'
OUT.mkdir(exist_ok=True)
EXAMPLES.mkdir(exist_ok=True)


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / (name + '.py'))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


FLAT = module('flat_control')
NESTED = module('nested_control')
INITIAL = [([0, 0, 0], [0, 1, 1])]


def rfl(t):
    return ['u', 0, t, []]


def zero(a, h):
    return ['v', rfl(a), rfl([0, a, h])]


def succ(c, a, h):
    return ['v', rfl([c, a, h]), rfl([[c], a, h])]


def join(p, q, source):
    return ['v', p, ['v', q, rfl([0, source, 1])]]


def reflexive_proof(a, scope=0):
    k, s, t = a
    assert s == t
    if k == 0:
        return rfl(s)
    body = FLAT.opening([k - 1, s, t], [0], 1)
    target = FLAT.opening(body, [-scope - 1])
    return ['i', a, [0], reflexive_proof(target, scope + 1)]


def nested_formula(a):
    k, s, t = a
    result = [s, t]
    for _ in range(k):
        result = [result]
    return result


def nested_proof(p):
    if p == []:
        return []
    tag = p[0]
    if tag == 'u':
        return [tag, p[1], p[2], nested_proof(p[3])]
    if tag in ('v', 'e'):
        return [tag, nested_proof(p[1]), nested_proof(p[2])]
    if tag == 'i':
        return [tag, nested_formula(p[1]), p[2], nested_proof(p[3])]
    raise ValueError('not a producer certificate')


def upstream_term(t):
    if type(t) is int:
        return t
    if len(t) == 1:
        return [0, upstream_term(t[0])]
    return [upstream_term(x) for x in t]


def upstream_formula(a):
    k, s, t = a
    result = [upstream_term(s), upstream_term(t)]
    for _ in range(k):
        result = [result]
    return result


def upstream_proof(p, context=INITIAL, conditional=(False,)):
    scope = len(context) - 1
    match p:
        case ['u', index, witness, premise]:
            base, body = context[index]
            if conditional[index]:
                if base[1] == base[2]:
                    premise = reflexive_proof(base, scope)
                premises = [upstream_proof(premise, context, conditional)]
            else:
                premises = []
            return ['u', index, upstream_term(witness), premises]
        case ['v', major, minor]:
            return ['v', upstream_proof(major, context, conditional),
                    upstream_proof(minor, context, conditional)]
        case ['e', major, branch]:
            k, s, t = FLAT.derive(major, context)
            body = FLAT.opening([k - 1, s, t], -scope - 1, 1)
            local = context + [(FLAT.opening(body, 0), body)]
            result = FLAT.derive(branch, local)
            return ['e', upstream_formula(result), upstream_proof(major, context, conditional),
                    upstream_proof(branch, local, conditional + (True,))]
        case ['i', goal, witness, branch]:
            k, s, t = goal
            body = FLAT.opening([k - 1, s, t], witness, 1)
            eta = -scope - 1 if k == 1 and witness == 0 else 0
            local = context + [([0, 0, 0], FLAT.opening(body, eta))]
            return ['i', upstream_formula(goal), upstream_term(witness),
                    upstream_proof(branch, local, conditional + (False,))]
        case _:
            raise ValueError('not a producer certificate')


def process(name, data, optimized=False):
    command = [sys.executable]
    if optimized:
        command.append('-O')
    command.append(str(ROOT / (name + '.py')))
    result = subprocess.run(command, input=json.dumps(data), text=True,
                            capture_output=True, timeout=10)
    return result.returncode == 0 and result.stdout == 'ACCEPT\n'


def generate_term(rng, scope, depth, fuel):
    leaves = list(range(-scope, depth + 1))
    if fuel == 0 or rng.randrange(3) == 0:
        return rng.choice(leaves)
    if rng.randrange(2):
        return [generate_term(rng, scope, depth, fuel - 1)]
    return [generate_term(rng, scope, depth, fuel - 1),
            generate_term(rng, scope, depth, fuel - 1),
            generate_term(rng, scope, depth + 1, fuel - 1)]


def measure(path):
    tree = ast.parse(path.read_text())
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.body and isinstance(node.body[0], ast.Expr) and isinstance(node.body[0].value, ast.Constant) and isinstance(node.body[0].value.value, str):
                node.body.pop(0)
    normalized = ast.unparse(tree) + '\n'
    omitted = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
               tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}
    tokens = sum(t.type not in omitted for t in tokenize.generate_tokens(io.StringIO(normalized).readline))
    compressed = gzip.compress(normalized.encode(), compresslevel=9, mtime=0)
    (OUT / (path.stem + '.normalized.py')).write_text(normalized)
    (OUT / (path.stem + '.normalized.py.gz')).write_bytes(compressed)
    return {'tokens': tokens, 'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'normalized_bytes': len(normalized.encode()), 'gzip9_bytes': len(compressed),
            'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def main():
    rng = random.Random(20261111)
    examples = {}
    examples['reflexivity_nested_iterator'] = rfl([[[0]], [0], [1]])
    examples['zero_computation'] = zero([0], [1])
    examples['successor_computation'] = succ([[0]], [0], [1])
    p = zero([0], [1])
    examples['derived_symmetry'] = join(rfl([0, [0], [1]]), p, [0, [0], [1]])
    equation = [1, [1, 0, [1]], 1]
    z = -1
    step = ['v', ['u', 1, 0, []], rfl([[z], 0, [1]])]
    induction = ['i', equation, 0, step]
    examples['equation_induction'] = induction
    examples['induction_specialization'] = ['e', induction, ['u', 1, [[0]], zero(0, [1])]]
    examples['nested_binders'] = reflexive_proof([4, [8, 7, [3, 0, 1]], [8, 7, [3, 0, 1]]])
    for index in range(30):
        k = rng.randrange(5)
        term = generate_term(rng, 0, 2 * k, 3)
        examples[f'random_reflexivity_{index:02d}'] = reflexive_proof([k, term, term])

    process_checks = []
    for name, proof in examples.items():
        goal = FLAT.derive(proof, INITIAL)
        flat = {'goal': goal, 'proof': proof}
        nested = {'goal': nested_formula(goal), 'proof': nested_proof(proof)}
        uniform = {'goal': upstream_formula(goal), 'proof': upstream_proof(proof)}
        if not name.startswith('random_'):
            (EXAMPLES / (name + '.json')).write_text(json.dumps(flat, indent=2) + '\n')
        for checker, data in [('flat_control', flat), ('nested_control', nested), ('reference_uniform', uniform)]:
            for optimized in (False, True):
                passed = process(checker, data, optimized)
                process_checks.append({'case': name, 'checker': checker, 'optimized': optimized,
                                       'expected': True, 'actual': passed})
                if not passed:
                    raise AssertionError(process_checks[-1])

    negative = {
        'false_equation': {'goal': [0, 0, [0]], 'proof': rfl(0)},
        'negative_height': {'goal': [-1, 0, 0], 'proof': rfl(0)},
        'boolean_height': {'goal': [False, 0, 0], 'proof': rfl(0)},
        'float_height': {'goal': [0.0, 0, 0], 'proof': rfl(0)},
        'out_of_scope_bound': {'goal': [1, 3, 3], 'proof': rfl(0)},
        'free_goal': {'goal': [0, -1, -1], 'proof': rfl(0)},
        'boolean_term': {'goal': [0, False, False], 'proof': rfl(0)},
        'invalid_term_arity': {'goal': [0, [0, 0], [0, 0]], 'proof': rfl(0)},
        'empty_term': {'goal': [0, [], []], 'proof': rfl(0)},
        'use_boolean_index': {'goal': [0, 0, 0], 'proof': ['u', False, 0, []]},
        'use_bad_index': {'goal': [0, 0, 0], 'proof': ['u', 1, 0, []]},
        'use_negative_index': {'goal': [0, 0, 0], 'proof': ['u', -1, 0, []]},
        'use_free_witness': {'goal': [0, 0, 0], 'proof': ['u', 0, -1, []]},
        'use_bound_witness': {'goal': [0, 0, 0], 'proof': ['u', 0, 1, []]},
        'intro_free_witness': {'goal': equation, 'proof': ['i', equation, -1, step]},
        'elimination_eigenparameter_escape': {'goal': [0, 0, 0], 'proof': ['e', induction, rfl(-1)]},
        'evaluation_compound_major': {'goal': [0, 0, 0], 'proof': ['v', induction, rfl([0, 0, 1])]},
        'unknown_rule': {'goal': [0, 0, 0], 'proof': ['invalid']},
        'extra_rule_field': {'goal': [0, 0, 0], 'proof': ['u', 0, 0, [], 0]},
        'wrong_goal_fields': {'goal': [0, 0], 'proof': rfl(0)},
        'unexpected_top_key': {'goal': [0, 0, 0], 'proof': rfl(0), 'extra': 0},
    }
    broken = copy.deepcopy(induction)
    broken[3] = rfl(0)
    negative['wrong_induction_step'] = {'goal': equation, 'proof': broken}
    for name, data in negative.items():
        for optimized in (False, True):
            actual = process('flat_control', data, optimized)
            process_checks.append({'case': name, 'checker': 'flat_control', 'optimized': optimized,
                                   'expected': False, 'actual': actual})
            if actual:
                raise AssertionError(process_checks[-1])

    structural = 0
    for _ in range(2000):
        scope, k, offset = rng.randrange(4), rng.randrange(5), rng.randrange(2)
        witness = generate_term(rng, scope, 0, 3)
        terms = [generate_term(rng, scope, 2 * k + offset + 1, 3) for _ in range(2)]
        a = [k, *terms]
        left = nested_formula(FLAT.opening(a, witness, offset))
        right = NESTED.opening(nested_formula(a), witness, offset)
        if left != right:
            raise AssertionError({'opening': a, 'witness': witness, 'offset': offset})
        structural += 1

    # An explicit nonvacuous witness-opening case preserves the inner binder.
    a = [2, [5, 0, 2], [6, 0, 1]]
    assert nested_formula(FLAT.opening(a, [0], 1)) == NESTED.opening(nested_formula(a), [0], 1)

    metrics = {name: measure(ROOT / (name + '.py')) for name in
               ('flat_control', 'nested_control', 'reference_uniform', 'flat_homogeneous')}
    report = {'python': platform.python_version(), 'metrics': metrics,
              'positive_certificates': len(examples), 'negative_cases': len(negative),
              'process_checks': len(process_checks), 'opening_commutations': structural + 1,
              'mismatches': sum(x['actual'] != x['expected'] for x in process_checks),
              'checks': process_checks,
              'limitations': ['Finite tests are implementation evidence, not proofs of soundness or completeness.',
                              'A Use premise is inert when its base has identical final terms.',
                              'Interpreter recursion and resource bounds are outside ideal finite derivation semantics.']}
    (OUT / 'checker_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    (OUT / 'checker_metrics.json').write_text(json.dumps({'python': platform.python_version(), 'metrics': metrics}, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('checks',)}, indent=2))


if __name__ == '__main__':
    main()
