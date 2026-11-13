#!/usr/bin/env python3
"""Read-only comparison of P64's historical source pins and retained payloads."""
import gzip
import hashlib
import json
import subprocess
from pathlib import Path

if not __debug__:
    raise SystemExit('refusing optimized Python')
ROOT = Path(__file__).resolve().parents[2]
PACKAGE = ROOT / 'con-zfc-diophantine-forms/64-structural-reductions/positive14'
RETAINED = ROOT / 'candidates/ten-positive-shifted-strong/coefficients'
PINS_SHA = '39add51f77110e9fe9b55601c98693cdaa541d162d6bb9d7833bb1f80547aa9c'
GRAPH_SHA = 'b9731360a30bcbcfd6f9161241cafb01b8c5d68aa40b84ddc50ba689a0745d0e'

def sha(data):
    return hashlib.sha256(data).hexdigest()

pins_bytes = (PACKAGE / 'SOURCE_PINS.json').read_bytes()
assert sha(pins_bytes) == PINS_SHA
assert sha((PACKAGE / 'polynomial.json').read_bytes()) == GRAPH_SHA
pins = json.loads(pins_bytes)['files']
assert len(pins) == 40 and len({e['path'] for e in pins}) == 40
missing, present, blobs = [], [], {}
for e in pins:
    path = PACKAGE / e['path']
    if path.is_file():
        assert sha(path.read_bytes()) == e['sha256'], e['path']
        present.append(e['path'])
    else:
        missing.append(e['path'])
    actual = subprocess.run(['git', 'rev-parse', e['commit'] + ':' + e['source_path']],
                            cwd=ROOT, text=True, capture_output=True, check=True).stdout.strip()
    assert actual == e['git_blob_sha1'], e['path']
    data = subprocess.run(['git', 'cat-file', 'blob', e['git_blob_sha1']],
                          cwd=ROOT, capture_output=True, check=True).stdout
    assert sha(data) == e['sha256'], e['path']
    blobs[e['path']] = data
assert len(present) == 6 and len(missing) == 34
payloads = {}
for name in ('beta.bin.gz', 'K.bin.gz', 'MC.bin.gz', 'MF_source.bin.gz'):
    data = (RETAINED / name).read_bytes()
    assert data == blobs['native/coefficients/' + name], name
    plain = gzip.decompress(data)
    payloads[name] = {'gzip_sha256': sha(data), 'decoded_sha256': sha(plain),
                      'decoded_bytes': len(plain)}
assert 'native/COEFFICIENT_BINDING.json' in missing
print(json.dumps({'status': 'PASS', 'pinned_paths': len(pins),
                  'present_package_paths': len(present), 'missing_package_paths': len(missing),
                  'historical_git_paths_and_blobs_matched': len(pins),
                  'missing_binding_blob_sha256': sha(blobs['native/COEFFICIENT_BINDING.json']),
                  'payloads_equal_retained_copies': payloads,
                  'scope': 'external byte comparison; no Lean port or PDF semantics'}, indent=2))
