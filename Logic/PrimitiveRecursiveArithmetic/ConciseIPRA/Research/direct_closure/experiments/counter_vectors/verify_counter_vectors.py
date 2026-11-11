"""Reproduce the counter-vector protocol comparison; no checker imports this."""
import ast
import copy
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SUPPORT = ROOT / 'baseline/coverage_and_kernel/tests'
sys.path.insert(0, str(SUPPORT))
import inherited_verify
import producer


def local_examples():
    previous = producer.Emitter

    class LocalEmitter(previous):
        def emit(self, proof, context):
            saved = self.floor
            self.floor = -len(context)
            try:
                return super().emit(proof, context)
            finally:
                self.floor = saved

    producer.Emitter = LocalEmitter
    try:
        return inherited_verify.cases()
    finally:
        producer.Emitter = previous


def counter_vectors(packet):
    packet = copy.deepcopy(packet)
    for command in packet[:-1]:
        if isinstance(command, list) and len(command) == 4:
            major, source, initializer, update = command
            if major == [] and initializer:
                command[1] = [source] if source else []
    return packet


def accepts(path, packet, optimized=False):
    result = subprocess.run(
        [sys.executable] + (['-O'] if optimized else []) + [str(path)],
        input=json.dumps(packet), text=True, capture_output=True, timeout=15)
    return result.returncode == 0 and result.stdout == 'ACCEPT\n'


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef,
                             ast.AsyncFunctionDef)) and node.body:
            first = node.body[0]
            if (isinstance(first, ast.Expr) and isinstance(first.value, ast.Constant)
                    and isinstance(first.value.value, str)):
                del node.body[0]
    source = (ast.unparse(tree) + '\n').encode()
    excluded = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
                tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(token.type not in excluded for token in
                 tokenize.generate_tokens(io.StringIO(source.decode()).readline))
    return {'raw_bytes': len(raw), 'normalized_bytes': len(source),
            'tokens': tokens, 'ast_nodes': len(list(ast.walk(tree))),
            'gzip9_raw_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
            'gzip9_normalized_bytes': len(gzip.compress(source, compresslevel=9, mtime=0)),
            'sha256': hashlib.sha256(raw).hexdigest()}


def main():
    examples = local_examples()
    programs = [ROOT / 'counter_vector_checker.py',
                ROOT / 'counter_vector_readable.py']
    baseline = ROOT / 'baseline/neutral_scope/code/checker.py'
    rows = []
    for case in examples:
        packet = counter_vectors(case['packet'])
        for optimized in (False, True):
            accepted = accepts(baseline, case['packet'], optimized)
            rows.append({'case': case['name'], 'program': 'baseline529',
                         'optimized': optimized, 'expected': case['accept'],
                         'accepted': accepted, 'ok': accepted == case['accept']})
            for path in programs:
                accepted = accepts(path, packet, optimized)
                rows.append({'case': case['name'], 'program': path.name,
                             'optimized': optimized, 'expected': case['accept'],
                             'accepted': accepted, 'ok': accepted == case['accept']})

    step_zero = [[[], [0], [0], 3], [[[0], [0], 3], [0, [0], 3]]]
    base = [[[], [], [0], 3], [[0, [0], 3], [0]]]
    step_annotation = copy.deepcopy(step_zero)
    step_annotation[0][1].append({'ignored': 'tail'})
    direct = [
        ('direct_successor_zero_identity', step_zero, True),
        ('direct_zero_counter', base, True),
        ('unused_counter_vector_tail', step_annotation, True),
        ('nonempty_string_counter', [[[], 'x', [0], 3], [0, [0]]], False),
        ('scalar_counter_rejected', [[[], 1, [0], 3], [0, [0]]], False),
        ('bare_false', [[0, [0]]], False),
    ]
    for name, packet, expected in direct:
        for path in programs:
            for optimized in (False, True):
                accepted = accepts(path, packet, optimized)
                rows.append({'case': name, 'program': path.name,
                             'optimized': optimized, 'expected': expected,
                             'accepted': accepted, 'ok': accepted == expected})

    # Dropping `or 0` causes this ordinary base certificate to fail.
    # This is a completeness gap, not a demonstrated false theorem.
    alias_candidate = ROOT / 'candidates/slice_bytes.py'
    alias_gap = {'candidate_bytes': 528,
                 'base_certificate': base,
                 'accepts_required_canonical_base': accepts(alias_candidate, base),
                 'claim': 'No canonical-zero alias conversion theorem has been established.'}
    metrics = {str(path.relative_to(ROOT)): measure(path)
               for path in [baseline] + programs}
    receipt = {'runtime': sys.version, 'inherited_examples': len(examples),
               'cli_checks': len(rows),
               'mismatches': sum(not row['ok'] for row in rows),
               'metrics': metrics, 'results': rows,
               'rejected_528_candidate': alias_gap,
               'finite_evidence_only': True}
    (ROOT / 'counter_vector_validation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    (ROOT / 'direct_successor_zero_identity.json').write_text(json.dumps(step_zero) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'results'}, indent=2))
    if receipt['mismatches']:
        print(json.dumps([row for row in rows if not row['ok']], indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
