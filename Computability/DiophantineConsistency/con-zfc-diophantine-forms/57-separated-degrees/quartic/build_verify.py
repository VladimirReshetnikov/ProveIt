#!/usr/bin/env python3
"""Emit and audit the 45-integer quartic by exact sparse arithmetic.

The source JSON is read only as data. No imported source code is executed.
This finite verifier does not prove the inherited Pell/compiler theorem.
"""
import ast
import hashlib
import itertools
import json
import gzip
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'quartic50_source.json'
parent = json.loads(SOURCE.read_text())
removed_guards = ('J', 'F', 'alpha', 'z')
removed = {f'{v}_pos{i}' for v in removed_guards for i in (1, 2, 3)}
added = ['q_half_root'] + [f'{v}_pos{i}' for v in ('FA', 'FC') for i in (1, 2, 3)]
variables = [v for v in parent['variables'] if v not in removed] + added
rows = [r for r in parent['residuals'] if not any(name in r for name in removed)]
rows += [
    'beta*J+1-2*q_half_root**2',
    'F*alpha-FA_pos1**2-FA_pos2**2-FA_pos3*(FA_pos3+1)-1',
    'F*(beta*J+1-F-alpha)-FC_pos1**2-FC_pos2**2-FC_pos3*(FC_pos3+1)-1',
]
fixed = parent['fixed_numerals']
pins = json.loads((HERE / 'SOURCE_PINS.json').read_text())
for record in pins['files']:
    raw = (HERE / record['local_path']).read_bytes()
    if hashlib.sha256(raw).hexdigest() != record['sha256']:
        raise ValueError('pinned source changed: ' + record['local_path'])
    git_blob = hashlib.sha1(f'blob {len(raw)}\0'.encode() + raw).hexdigest()
    if git_blob != record['git_blob_sha1']:
        raise ValueError('pinned Git blob changed: ' + record['local_path'])
payloads = HERE / 'upstream/34-integer14/coefficients/payloads'
binding = json.loads((payloads / 'COEFFICIENT_BINDING.json').read_text())
coefficient_values = {}
for name in ('beta', 'K', 'MC', 'MF_source'):
    raw = (payloads / (name + '.bin')).read_bytes()
    packed = (payloads / (name + '.bin.gz')).read_bytes()
    if gzip.decompress(packed) != raw or hashlib.sha256(raw).hexdigest() != binding['payloads'][name]['sha256']:
        raise ValueError('fixed coefficient mismatch: ' + name)
    coefficient_values[name] = int.from_bytes(raw, 'little')
if coefficient_values['beta'] != (1 << 1064921) - 1:
    raise ValueError('wrong native coefficient tuple')
names = variables + fixed
n = len(names)
zero = (0,) * n

def req(b, s):
    if not b:
        raise ValueError(s)

def const(k):
    return {} if not k else {zero: k}

def add(a, b):
    c = dict(a)
    for m, k in b.items():
        c[m] = c.get(m, 0) + k
        if not c[m]:
            del c[m]
    return c

def mul(a, b):
    c = {}
    for u, x in a.items():
        for v, y in b.items():
            m = tuple(i + j for i, j in zip(u, v))
            c[m] = c.get(m, 0) + x * y
    return {m: k for m, k in c.items() if k}

def parse(node):
    if isinstance(node, ast.Expression):
        return parse(node.body)
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return const(node.value)
    if isinstance(node, ast.Name):
        e = [0] * n
        e[names.index(node.id)] = 1
        return {tuple(e): 1}
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return mul(const(-1), parse(node.operand))
    if isinstance(node, ast.BinOp):
        a = parse(node.left)
        if isinstance(node.op, ast.Pow):
            req(isinstance(node.right, ast.Constant) and type(node.right.value) is int and node.right.value >= 0, 'nonnegative literal exponent required')
            b = const(1)
            for _ in range(node.right.value):
                b = mul(b, a)
            return b
        b = parse(node.right)
        if isinstance(node.op, ast.Add):
            return add(a, b)
        if isinstance(node.op, ast.Sub):
            return add(a, mul(const(-1), b))
        if isinstance(node.op, ast.Mult):
            return mul(a, b)
    raise ValueError('unsupported polynomial syntax')

polys = [parse(ast.parse(r, mode='eval')) for r in rows]
degrees = [max(sum(m[:len(variables)]) for m in p) for p in polys]
req(len(variables) == 45, 'variable count')
req(len(rows) == 28, 'equation count')
req(degrees == [2] * 28, 'quadratic residuals')
req(len(set(variables)) == 45, 'variable uniqueness')
req(all(any(any(m[i] for m in p) for p in polys) for i in range(len(variables))), 'all variables live')
Q = {}
for p in polys:
    Q = add(Q, mul(p, p))
req(max(sum(m[:len(variables)]) for m in Q) == 4, 'quartic degree')
tau4 = [0] * n
tau4[names.index('tau')] = 4
req(Q.get(tuple(tau4)) == 1, 'uniform tau^4 coefficient')
guard_cases = 0
for F, alpha, C in itertools.product(range(-8, 9), repeat=3):
    if F + alpha + C > 0 and F * alpha > 0 and F * C > 0:
        req(min(F, alpha, C) > 0, 'guard sign diagnostic')
        guard_cases += 1
radix_cases = 0
for beta in range(3, 40):
    for J in range(-50, 51):
        for v in range(-30, 31):
            if beta * J + 1 == 2 * v * v:
                req(J > 0, 'dyadic guard diagnostic')
                radix_cases += 1
packet = {
    'name': 'quartic45_common_sign_dyadic_guard',
    'domain': 'unrestricted integers',
    'variables': variables,
    'variable_count': 45,
    'equation_count': 28,
    'fixed_numerals': fixed,
    'coefficient_binding': {
        'manifest': 'upstream/34-integer14/COEFFICIENT_BINDING.json',
        'compiler_manifest': 'upstream/34-integer14/coefficients/payloads/COEFFICIENT_BINDING.json',
        'mask_convention': 'MF is the already shifted MF_source',
        'transfer_proof': 'upstream/34-integer14/coefficients/COEFFICIENT_PROOF.md',
        'ports': {'beta':'beta', 'K0':'K', 'MC':'MC', 'MF':'MF_source'}
    },
    'residuals': rows,
    'residual_degrees': degrees,
    'single_polynomial': 'sum of squares of listed residuals',
    'exact_degree': 4,
    'exact_degree_certificate': 'coefficient of tau^4 is 1',
    'parent_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    'source_pin': '4b4349064a750ba6347293b55874a7f92abdd0db',
    'proof': 'QUARTIC45_PROOF.md',
    'status': 'Ordinary mathematical reduction with inherited Pell/compiler dependencies; no new kernel certificate.'
}
(HERE / 'quartic45.json').write_text(json.dumps(packet, indent=2) + '\n')
expanded = {'variables': names, 'terms': [{'coefficient': k, 'exponents': list(m)} for m, k in sorted(Q.items())]}
(HERE / 'quartic45_expanded.json').write_text(json.dumps(expanded, separators=(',', ':')) + '\n')
receipt = {
    'status': 'PASS', 'variables': len(variables), 'equations': len(rows),
    'residual_degrees': degrees, 'exact_degree': 4, 'tau4_coefficient': 1,
    'symbolic_terms': len(Q), 'guard_sign_diagnostic_cases': guard_cases,
    'dyadic_guard_diagnostic_cases': radix_cases,
    'parent_sha256': packet['parent_sha256'],
    'pinned_source_files_checked': len(pins['files']),
    'native_payloads_checked': 4,
    'finite_check_boundary': 'The sign/radix loops are diagnostics; the universal proofs are in QUARTIC45_PROOF.md. The polynomial identities and exact degree are checked symbolically.'
}
(HERE / 'AUDIT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
