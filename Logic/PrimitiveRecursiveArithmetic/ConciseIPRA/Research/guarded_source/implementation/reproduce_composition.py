"""Reproduce certificates, process checks, and whole-module measurements."""

import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'guarded_core' / 'tests'))
import build_root_cases as b
import composition_producer as c

SELECTED = {
    'exactroot_checker_tokens.py': ('global', False, False),
    'exactroot_checker_ast.py': ('local', True, True),
    'exactroot_checker_bytes.py': ('local', True, True),
}


def extra_proofs():
    p = c.p
    h = c.n.fresh('transport_parameter')
    zero = p.I(0, 0, c.n.fresh('boxed_zero'), 0)
    major = c.n.sym(p.compute(zero))
    equation = p.Eq(p.V(h), 0)
    motive = b.lift_formula(equation)
    source = p.substitute(motive, h, 0)
    minor = b.lift_intro(p.reflexivity(0, c.n.fresh('refl')), source)
    direct = p.transport(major, h, motive, minor)
    _, _, index, matrix = motive
    qminor = p.elimination(minor, c.n.fresh('q_extract'),
        p.hyp(p.Q(index, p.substitute(matrix, h, 0))))
    qproof = p.transport(major, h, p.Q(index, matrix), qminor)
    cmotive = b.implication(equation, equation)
    cleft = p.substitute(equation, h, 0)
    cminor = b.implication_intro(cleft, cleft, p.hyp(cleft),
                               p.substitute(cmotive, h, 0))
    compound = p.transport(major, h, cmotive, cminor)
    return [
        {'name': 'zero_transport_guarded_D', 'proof': direct,
         'expected': True, 'canonical_goal': True},
        {'name': 'zero_transport_guarded_Q', 'proof': qproof,
         'expected': True, 'canonical_goal': False},
        {'name': 'zero_transport_compound_D', 'proof': compound,
         'expected': True, 'canonical_goal': True},
    ]


def run(checker, data, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / checker)]
    result = subprocess.run(command, input=data, capture_output=True, timeout=30)
    return result.returncode == 0 and result.stdout == b'ACCEPT\n'


def metrics():
    ignored = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
               tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
               tokenize.ENDMARKER}
    rows = []
    names = list(SELECTED) + ['exactroot_strict_checker.py',
        'source_dispatch_code_checker_tokens.py',
        'source_dispatch_code_checker.py',
        'source_dispatch_code_checker_bytes.py',
        'guarded_core_code_strict_checker.py']
    for name in names:
        source = (ROOT / name).read_bytes()
        normalized = (ast.unparse(ast.parse(source)) + '\n').encode()
        compressed = gzip.compress(normalized, compresslevel=9, mtime=0)
        rows.append({
            'file': name,
            'significant_tokens': sum(t.type not in ignored for t in
                tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
            'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
            'normalized_bytes': len(normalized),
            'gzip9_normalized_bytes': len(compressed),
            'sha256': hashlib.sha256(source).hexdigest(),
        })
        if name in SELECTED or name == 'exactroot_strict_checker.py':
            (ROOT / (name + '.gz')).write_bytes(compressed)
    result = {'python': sys.version, 'zlib': zlib.ZLIB_VERSION,
        'normalization': 'ast.unparse(ast.parse(source)) + newline',
        'gzip': 'gzip.compress(normalized_bytes, compresslevel=9, mtime=0)',
        'metrics': rows}
    (ROOT / 'metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    return rows


def main():
    directory = ROOT / 'composed_tests'
    directory.mkdir(exist_ok=True)
    cases = b.build_proofs() + extra_proofs()
    receipts, audits = [], []
    zero_packet = None
    for case in cases:
        if not case['expected']:
            continue
        proof = c.transform(case['proof'])
        audit = c.audit(proof)
        if audit['forbidden_zero_sources'] or audit['wrong_introduction_modes']:
            raise RuntimeError({'case': case['name'], 'audit': audit})
        audits.append({'name': case['name'], **audit})
        packets = {}
        for flavor, lexical, neutral in set(SELECTED.values()):
            packet = b.make_packet(proof, lexical, neutral)
            data = (json.dumps(packet, separators=(',', ':')) + '\n').encode()
            filename = case['name'] + '_' + flavor + '.json'
            (directory / filename).write_bytes(data)
            packets[flavor] = (filename, data, len(packet) - 1)
            if case['name'] == 'computation_zero' and flavor == 'local':
                zero_packet = packet
        for checker, (flavor, _, _) in SELECTED.items():
            filename, data, instructions = packets[flavor]
            for optimized in (False, True):
                accepted = run(checker, data, optimized)
                receipts.append({'checker': checker, 'case': filename,
                    'optimized': optimized, 'expected': True, 'accepted': accepted,
                    'bytes': len(data), 'instructions': instructions})
        filename, data, instructions = packets['local']
        for optimized in (False, True):
            accepted = run('exactroot_strict_checker.py', data, optimized)
            receipts.append({'checker': 'exactroot_strict_checker.py',
                'case': filename, 'optimized': optimized,
                'expected': case['canonical_goal'], 'accepted': accepted,
                'bytes': len(data), 'instructions': instructions})

    wrong_endpoint = json.loads(json.dumps(zero_packet))
    wrong_endpoint[-1][1] = 0
    negative = {
        'false_zero_equals_one': [[0, [0]]],
        'missing_goal': [],
        'missing_instruction_fields': [[0], [0, [0]]],
        'null_goal': [None],
        'wrong_computation_endpoint': wrong_endpoint,
        'missing_computation': [zero_packet[-1]],
    }
    old_case = next(x for x in cases if x['name'] == 'old_atomic_case_D_y_eq_one')
    for checker, (flavor, lexical, neutral) in SELECTED.items():
        controls = dict(negative)
        controls['old_atomic_case'] = b.make_packet(old_case['proof'], lexical, neutral)
        for name in ('context_leak_attack', 'future_witness_capture'):
            controls[name] = json.loads((ROOT / 'tests' / (name + '.json')).read_text())
        for name, packet in controls.items():
            data = (json.dumps(packet, separators=(',', ':')) + '\n').encode()
            filename = name + '_' + flavor + '.json'
            (directory / filename).write_bytes(data)
            for optimized in (False, True):
                receipts.append({'checker': checker, 'case': filename,
                    'optimized': optimized, 'expected': False,
                    'accepted': run(checker, data, optimized), 'bytes': len(data)})

    failures = [r for r in receipts if r['accepted'] != r['expected']]
    report = {'executions': len(receipts),
        'expected_acceptances': sum(r['expected'] for r in receipts),
        'expected_rejections': sum(not r['expected'] for r in receipts),
        'failures': failures, 'receipts': receipts, 'named_proof_audits': audits}
    (ROOT / 'validation.json').write_text(json.dumps(report, indent=2) + '\n')
    measured = metrics()
    print(json.dumps({k: report[k] for k in ('executions', 'expected_acceptances',
          'expected_rejections', 'failures')}, indent=2))
    for row in measured:
        print(row)
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
