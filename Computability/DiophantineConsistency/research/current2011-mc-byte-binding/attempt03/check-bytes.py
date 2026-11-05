#!/usr/bin/env python3
"""Evaluate the pinned six-run radix recipe and compare both MC gzip payloads."""
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
     TASK / 'candidates/one-page-padding-staircase-carrier65-2011/coefficients/MC.bin.gz'),
    (HERE.parent / 'fourteen-normalized-product106/polynomial.json',
     '0485cd1e884b918d766261b1780be117238f0813a965c6d8ae4d805176a5f6e1',
     HERE.parent / 'fourteen-normalized-product106/coefficients/MC.bin.gz'),
]
SOURCE = HERE / 'CurrentMCBytes.lean'
sha = lambda b: hashlib.sha256(b).hexdigest()
source = SOURCE.read_bytes()
if sha(source) != '426d17ea20f5fa18ac2a1b905bae1d61a76fa09ffe33cda43727baacf343f764':
    raise SystemExit('Lean source mismatch')
text = source.decode()
if 'def rho : ℕ := 2^47' not in text or 'def bigBytes : List ℕ := (Nat.digits 256 (Nat.ofDigits rho maskDigits)).reverse' not in text:
    raise SystemExit('unexpected radix or byte conversion recipe')
body = text.split('def maskDigits : List ℕ :=', 1)[1].split('/-- Canonical', 1)[0]
runs = [(int(n), int(offset)) for n, offset in re.findall(r'List\.replicate (\d+) \(rho-(\d+)\)', body)]
if runs != [(951, 2), (9, 1), (26, 2), (18, 1), (1, 2), (1006, 1)]:
    raise SystemExit('unexpected radix-digit runs')
rho = 2**47
digits = [rho - offset for count, offset in runs for _ in range(count)]
n = 0
for digit in reversed(digits):
    n = rho * n + digit
expected = n.to_bytes((n.bit_length() + 7) // 8, 'big')
results = []
for graph, graph_sha, payload in SOURCES:
    data = graph.read_bytes()
    if sha(data) != graph_sha:
        raise SystemExit('graph drift: ' + str(graph))
    metadata = json.loads(data)['coefficient_binding']['ports']['MC']
    compressed = payload.read_bytes()
    if sha(compressed) != metadata['gzip_sha256']:
        raise SystemExit('compressed payload drift: ' + str(payload))
    raw = gzip.decompress(compressed)
    if sha(raw) != metadata['raw_sha256'] or len(raw) != metadata['raw_bytes']:
        raise SystemExit('raw payload drift: ' + str(payload))
    if raw != expected or n.bit_length() != metadata['bits']:
        raise SystemExit('byte recipe mismatch: ' + str(payload))
    results.append({'graph': str(graph.relative_to(TASK)), 'payload': str(payload.relative_to(TASK)),
                    'gzip_sha256': sha(compressed), 'raw_sha256': sha(raw), 'raw_bytes': len(raw),
                    'byte_order': 'big', 'bits': n.bit_length()})
if SOURCE.read_bytes() != source:
    raise SystemExit('Lean source changed')
print(json.dumps({'status': 'PASS', 'source_sha256': sha(source), 'radix_digit_runs': runs,
                  'radix_digits': len(digits), 'results': results}, indent=2, sort_keys=True))
