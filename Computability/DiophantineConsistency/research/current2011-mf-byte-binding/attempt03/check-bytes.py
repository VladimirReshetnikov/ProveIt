#!/usr/bin/env python3
"""Evaluate the pinned beta-shifted radix recipe and compare both MF payloads."""
import gzip
import hashlib
import json
import re
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
TASK = HERE.parents[1]
SOURCES = [
    (HERE.parent / 'current2011-unscaled66/polynomial.json',
     'bf9e05905fe84f74edade75ba7d373bd6955aa035867af89a6026d9a21719e75',
     TASK / 'candidates/one-page-padding-staircase-carrier65-2011/coefficients/MF_source.bin.gz'),
    (HERE.parent / 'fourteen-normalized-product106/polynomial.json',
     '0485cd1e884b918d766261b1780be117238f0813a965c6d8ae4d805176a5f6e1',
     HERE.parent / 'fourteen-normalized-product106/coefficients/MF_source.bin.gz'),
]
SOURCE = HERE / 'CurrentMFBytes.lean'
sha = lambda b: hashlib.sha256(b).hexdigest()
source = SOURCE.read_bytes()
if sha(source) != '7fef6b149540a6a2f83cad2d73b3211780f288b221073f3a6b3cfee9551cf235':
    raise SystemExit('Lean source mismatch')
text = source.decode()
for expression in ('def rho : ℕ := 2^47',
                   'def shiftedValue : ℕ := Nat.ofDigits rho maskDigits + (rho^2011 - 1)',
                   'def bigBytes : List ℕ := (Nat.digits 256 shiftedValue).reverse'):
    if expression not in text:
        raise SystemExit('unexpected radix, shift, or byte conversion recipe')
body = text.split('def maskDigits : List ℕ :=', 1)[1].split('theorem rho_eq', 1)[0]
runs = [(int(n), int(value)) for n, value in re.findall(r'List\.replicate (\d+) (\d+)', body)]
if runs != [(916, 8), (43, 0), (9, 1), (18, 0), (8, 1), (9, 0), (1005, 0)]:
    raise SystemExit('unexpected radix-digit runs')
if '(4 :: (' not in body or '[1, 2^45-4]' not in body:
    raise SystemExit('unexpected fixed radix-digit entries')
rho = 2**47
digits = [4]
for count, value in runs[:-1]:
    digits.extend([value] * count)
digits.extend([1, 2**45-4])
digits.extend([runs[-1][1]] * runs[-1][0])
unshifted = 0
for digit in reversed(digits):
    unshifted = rho * unshifted + digit
beta = rho**2011 - 1
shifted = unshifted + beta
expected = shifted.to_bytes((shifted.bit_length() + 7) // 8, 'big')
results = []
for graph, graph_sha, payload in SOURCES:
    data = graph.read_bytes()
    if sha(data) != graph_sha:
        raise SystemExit('graph drift: ' + str(graph))
    metadata = json.loads(data)['coefficient_binding']['ports']['MF']
    compressed = payload.read_bytes()
    if sha(compressed) != metadata['gzip_sha256']:
        raise SystemExit('compressed payload drift: ' + str(payload))
    raw = gzip.decompress(compressed)
    if sha(raw) != metadata['raw_sha256'] or len(raw) != metadata['raw_bytes']:
        raise SystemExit('raw payload drift: ' + str(payload))
    if raw != expected or shifted.bit_length() != metadata['bits']:
        raise SystemExit('shifted byte recipe mismatch: ' + str(payload))
    if raw == unshifted.to_bytes((unshifted.bit_length() + 7) // 8, 'big'):
        raise SystemExit('payload unexpectedly equals unshifted high mask')
    results.append({'graph': str(graph.relative_to(TASK)), 'payload': str(payload.relative_to(TASK)),
                    'gzip_sha256': sha(compressed), 'raw_sha256': sha(raw), 'raw_bytes': len(raw),
                    'byte_order': 'big', 'bits': shifted.bit_length()})
if SOURCE.read_bytes() != source:
    raise SystemExit('Lean source changed')
print(json.dumps({'status': 'PASS', 'source_sha256': sha(source), 'radix_digit_runs': runs,
                  'radix_digits': len(digits), 'beta_shifts': 1, 'results': results}, indent=2, sort_keys=True))
