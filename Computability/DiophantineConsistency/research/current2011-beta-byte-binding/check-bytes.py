#!/usr/bin/env python3
"""Compare both retained gzip payloads to the explicit Lean big-endian recipe."""
import gzip
import hashlib
import json
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
TASK = HERE.parents[1]
SOURCES = [
    (HERE.parent / 'current2011-unscaled66/polynomial.json',
     'bf9e05905fe84f74edade75ba7d373bd6955aa035867af89a6026d9a21719e75',
     TASK / 'candidates/one-page-padding-staircase-carrier65-2011/coefficients/beta.bin.gz'),
    (HERE.parent / 'fourteen-normalized-product106/polynomial.json',
     '0485cd1e884b918d766261b1780be117238f0813a965c6d8ae4d805176a5f6e1',
     HERE.parent / 'fourteen-normalized-product106/coefficients/beta.bin.gz'),
]
SOURCE = HERE / 'CurrentBetaBytes.lean'
sha = lambda b: hashlib.sha256(b).hexdigest()
source = SOURCE.read_bytes()
if sha(source) != '538444983d5a713194673f3e17377e234bbce33d27d0f3cffa37d4a1eff762c8':
    raise SystemExit('Lean source mismatch')
if source.count(b'def bigBytes : List \xe2\x84\x95 := 31 :: List.replicate 11814 255') != 1:
    raise SystemExit('unexpected byte recipe')
expected = bytes([31]) + bytes([255]) * 11814
results = []
for graph, graph_sha, payload in SOURCES:
    data = graph.read_bytes()
    if sha(data) != graph_sha:
        raise SystemExit('graph drift: ' + str(graph))
    metadata = json.loads(data)['coefficient_binding']['ports']['beta']
    compressed = payload.read_bytes()
    if sha(compressed) != metadata['gzip_sha256']:
        raise SystemExit('compressed payload drift: ' + str(payload))
    raw = gzip.decompress(compressed)
    if sha(raw) != metadata['raw_sha256'] or len(raw) != metadata['raw_bytes']:
        raise SystemExit('raw payload drift: ' + str(payload))
    if raw != expected or int.from_bytes(raw, 'big').bit_length() != metadata['bits']:
        raise SystemExit('byte recipe mismatch: ' + str(payload))
    results.append({'graph': str(graph.relative_to(TASK)), 'payload': str(payload.relative_to(TASK)),
                    'gzip_sha256': sha(compressed), 'raw_sha256': sha(raw), 'raw_bytes': len(raw),
                    'byte_order': 'big', 'bits': metadata['bits']})
if SOURCE.read_bytes() != source:
    raise SystemExit('Lean source changed')
print(json.dumps({'status': 'PASS', 'source_sha256': sha(source), 'results': results}, indent=2, sort_keys=True))
