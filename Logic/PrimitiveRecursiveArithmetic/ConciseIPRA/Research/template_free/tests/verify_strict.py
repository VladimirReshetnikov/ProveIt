"""Rebuild and verify the strict R and matched X certificates and metrics.

Run from any directory: python3 path/to/tests/verify_strict.py
Only the standard library is used. This script is untrusted test support;
none of the four standalone checkers imports it or the proof producer.
"""
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
import zlib
from pathlib import Path

import generate_strict_certificates as producer


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'tests' / 'strict_certificates'
EVIDENCE = ROOT / 'evidence'
PROGRAMS = [
    ('global_rewrite', ROOT / 'code' / 'global_rewrite.py', 'rw'),
    ('one_context_original_walk', ROOT / 'reference' / 'one_context_seven.py', 'tr'),
    ('one_context_callback_walk', ROOT / 'reference' / 'one_context_seven_shared_walk.py', 'tr'),
    ('one_context_unified_walk', ROOT / 'reference' / 'one_context_seven_unified_walk.py', 'tr'),
]


def canonical_source(path):
    tree = ast.parse(path.read_text())
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and isinstance(node.body[0].value.value, str)):
                node.body.pop(0)
    return tree, (ast.unparse(tree) + '\n').encode()


def measurements():
    rows = []
    (EVIDENCE / 'gzip').mkdir(parents=True, exist_ok=True)
    skip = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
            tokenize.INDENT, tokenize.DEDENT, tokenize.NL, tokenize.NEWLINE}
    for name, path, _ in PROGRAMS:
        tree, data = canonical_source(path)
        packed = gzip.compress(data, compresslevel=9, mtime=0)
        (EVIDENCE / 'gzip' / (name + '.py.gz')).write_bytes(packed)
        rows.append({
            'name': name, 'path': str(path.relative_to(ROOT)),
            'raw_bytes': path.stat().st_size, 'normalized_bytes': len(data),
            'significant_tokens': sum(t.type not in skip for t in tokenize.tokenize(io.BytesIO(data).readline)),
            'ast_nodes': len(list(ast.walk(tree))), 'gzip9_normalized_bytes': len(packed),
            'sha256_raw': hashlib.sha256(path.read_bytes()).hexdigest(),
            'sha256_normalized': hashlib.sha256(data).hexdigest(),
        })
    receipt = {
        'python': sys.version, 'implementation': platform.python_implementation(),
        'zlib_compile_version': zlib.ZLIB_VERSION, 'zlib_runtime_version': zlib.ZLIB_RUNTIME_VERSION,
        'contract': 'Whole standalone strict tagged module; ast.unparse plus LF; gzip level 9, mtime 0.',
        'programs': rows,
    }
    (EVIDENCE / 'strict_metrics.json').write_text(json.dumps(receipt, indent=2) + '\n')
    labels = {'global_rewrite': 'Template-free global replacement',
              'one_context_original_walk': 'One-context X: original traversal',
              'one_context_callback_walk': 'One-context X: callback traversal',
              'one_context_unified_walk': 'One-context X: unified traversal'}
    table = [r'\begin{tabular}{@{}p{0.46\linewidth}rrrr@{}}', r'\toprule',
             r'Complete standalone module & Bytes & Tokens & AST & Gzip-9\\', r'\midrule']
    for row in rows[1:] + rows[:1]:
        table.append(f"{labels[row['name']]} & {row['normalized_bytes']} & {row['significant_tokens']} & {row['ast_nodes']} & {row['gzip9_normalized_bytes']}" + r'\\')
    table += [r'\bottomrule', r'\end{tabular}']
    (EVIDENCE / 'strict_metrics_table.tex').write_text('\n'.join(table) + '\n')
    return receipt


def controls(cases, tag):
    c = {name: copy.deepcopy(cert) for name, cert, _, _ in cases}
    z, one, v0 = ['z'], ['s', ['z']], ['v', 0]
    eq0, eq1 = ['=', z, z], ['=', one, one]
    base = c['root_reflexivity_zero']
    results = []

    def mutation(name, modify, original=base):
        cert = copy.deepcopy(original)
        modify(cert)
        results.append((name, cert, False, None))

    mutation('reject_extra_header_field', lambda a: a.update(extra=0))
    mutation('reject_boolean_variable_count', lambda a: a.update(variables=True))
    mutation('reject_negative_variable_count', lambda a: a.update(variables=-1))
    mutation('reject_free_variable_goal', lambda a: a.update(goal=['=', v0, v0]))
    mutation('reject_boolean_variable_index', lambda a: a.update(variables=1, goal=['=', ['v', False], ['v', False]]))
    hypothesis = {'variables': 0, 'context': [eq0], 'goal': eq0, 'proof': ['hyp', 0]}
    mutation('reject_boolean_hypothesis_index', lambda a: a.update(proof=['hyp', False]), hypothesis)
    mutation('reject_negative_hypothesis_index', lambda a: a.update(proof=['hyp', -1]), hypothesis)
    mutation('reject_out_of_range_hypothesis', lambda a: a.update(proof=['hyp', 1]), hypothesis)
    mutation('reject_invalid_initializer_scope', lambda a: a.update(proof=['zero', v0, z]))
    mutation('reject_invalid_update_scope', lambda a: a.update(proof=['zero', z, ['v', 1]]))
    mutation('reject_invalid_counter_scope', lambda a: a.update(proof=['succ', v0, z, z]))
    mutation('reject_wrong_zero_endpoint', lambda a: a.update(goal=['=', ['i', z, one, z], z], proof=['zero', one, z]))
    mutation('reject_formula_in_term_position', lambda a: a.update(proof=['zero', ['q', eq0], z]))
    mutation('reject_wrong_proof_arity', lambda a: a['proof'].append(0))
    mutation('reject_unknown_proof_rule', lambda a: a.update(proof=['unknown']))
    closure = ['q', ['=', v0, v0]]
    wrong_qe = {'variables': 0, 'context': [closure], 'goal': eq1,
                'proof': ['qe', one, ['hyp', 0], producer.certificate(producer.refl(producer.S(0)), rw_tag=tag)['proof']]}
    results.append(('reject_wrong_QE_base', wrong_qe, False, None))
    wrong_major = copy.deepcopy(base)
    wrong_major['proof'] = ['qe', one, copy.deepcopy(base['proof']), copy.deepcopy(base['proof'])]
    results.append(('reject_equation_as_Q_major', wrong_major, False, None))
    qproof = c['used_hypothesis_progress']['proof']
    rule = (lambda p, q: ['rw', p, q]) if tag == 'rw' else (lambda p, q: ['tr', v0, p, q])
    mutation('reject_non_equation_rewrite_major', lambda a: a.update(proof=rule(copy.deepcopy(qproof), copy.deepcopy(base['proof']))))
    mutation('reject_non_equation_rewrite_minor', lambda a: a.update(proof=rule(copy.deepcopy(base['proof']), copy.deepcopy(qproof))))
    mutation('reject_DI_witness_escape', lambda a: a['proof'][2].__setitem__(2, v0), c['used_hypothesis_progress'])
    mutation('reject_DE_witness_escape', lambda a: a['proof'].__setitem__(1, ['=', v0, v0]), c['used_hypothesis_progress'])
    return results


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def traversal_checks():
    """Target the new unified traversal, independently of certificate verdicts."""
    old = load_module('strict_old_control', PROGRAMS[1][1])
    new = load_module('strict_new_control', PROGRAMS[0][1])
    rng = random.Random(20261111)

    def tm(n, depth):
        if depth == 0:
            return ['v', rng.randrange(n)] if n and rng.randrange(2) else ['z']
        pick = rng.randrange(4)
        if pick < 2:
            return tm(n, 0)
        if pick == 2:
            return ['s', tm(n, depth - 1)]
        return ['i', tm(n, depth - 1), tm(n, depth - 1), tm(n + 1, depth - 1)]

    def fm(n, depth):
        if depth == 0 or rng.randrange(3) == 0:
            return ['=', tm(n, 3), tm(n, 3)]
        tag = rng.choice(['q', 'd'])
        return [tag, fm(n + (1 if tag == 'q' else 2), depth - 1)]

    counts = {'shift': 0, 'sub_drop_one': 0, 'sub_drop_zero': 0, 'root_rewrite': 0}
    for _ in range(200):
        n = rng.randrange(4)
        a = fm(n + 1, 3)
        target = tm(n, 3)
        for k in (0, 1, 2):
            if old.shift(a, k) != new.shift(a, k):
                raise ValueError('Shift mismatch')
            counts['shift'] += 1
        if old.sub(a, target) != new.sub(a, target):
            raise ValueError('Dropping substitution mismatch')
        counts['sub_drop_one'] += 1
        successor = ['s', ['v', 0]]
        if old.sub(a, successor, 0) != new.sub(a, successor, 0):
            raise ValueError('Non-dropping substitution mismatch')
        counts['sub_drop_zero'] += 1
        source = tm(n, 3)
        if new.walk(source, target, source, 0) != target:
            raise ValueError('Root rewriting mismatch')
        counts['root_rewrite'] += 1
    return {'seed': 20261111, 'counts': counts, 'comparisons': sum(counts.values()), 'mismatches': 0}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    families = {}
    for tag in ('rw', 'tr'):
        producer.serial = 0
        records = producer.cases(tag)
        records += controls(records, tag)
        family = {}
        destination = OUT / tag
        destination.mkdir(exist_ok=True)
        for name, cert, accept, _ in records:
            data = (json.dumps(cert, separators=(',', ':')) + '\n').encode()
            path = destination / (name + '.json')
            path.write_bytes(data)
            family[name] = {'path': path, 'expected_accept': accept, 'certificate': cert,
                            'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
        families[tag] = family
    if families['rw'].keys() != families['tr'].keys():
        raise ValueError('Different R/X fixture inventories')
    for name in families['rw']:
        r, x = (families[tag][name]['certificate'] for tag in ('rw', 'tr'))
        if any(r[key] != x[key] for key in ('variables', 'context', 'goal')):
            raise ValueError('R/X statements differ: ' + name)

    rows = []
    for name, path, tag in PROGRAMS:
        for optimized in (False, True):
            for case, record in families[tag].items():
                argv = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
                run = subprocess.run(argv, input=record['path'].read_bytes(), capture_output=True, timeout=30)
                accept = run.returncode == 0 and run.stdout == b'ACCEPT\n'
                rows.append({'program': name, 'case': case, 'optimized': optimized,
                             'expected_accept': record['expected_accept'], 'actual_accept': accept,
                             'matched': accept == record['expected_accept']})

    metrics = measurements()
    comparisons = traversal_checks()
    receipt = {'python': sys.version, 'programs': [p for p, _, _ in PROGRAMS],
               'cases_per_program': len(families['rw']), 'process_runs': len(rows),
               'expected_acceptances': sum(r['expected_accept'] for r in rows),
               'expected_rejections': sum(not r['expected_accept'] for r in rows),
               'matched': sum(r['matched'] for r in rows),
               'traversal_comparisons': comparisons,
               'failures': [r for r in rows if not r['matched']], 'runs': rows,
               'source_hashes': {r['path']: r['sha256_raw'] for r in metrics['programs']},
               'limits': 'Finite implementation checks, not a formal proof of soundness or bi-interpretability.'}
    (EVIDENCE / 'strict_validation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    manifest = {tag: {name: {key: str(value.relative_to(ROOT)) if key == 'path' else value
                             for key, value in record.items() if key != 'certificate'}
                      for name, record in family.items()} for tag, family in families.items()}
    (OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({key: value for key, value in receipt.items() if key not in ('runs', 'source_hashes')}, indent=2))
    if receipt['failures']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
