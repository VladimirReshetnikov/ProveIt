#!/usr/bin/env python3
"""Verify the packaged byte manifest and declared consistency checks."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = json.loads((root / 'MANIFEST.json').read_text())
for name, expected in manifest['files'].items():
    path = root / name
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit('Digest mismatch: ' + name)
result = json.loads((root / 'verification/result.json').read_text())
if result['status'] != 'PASS_FOCUSED_BASELINE_AND_CANDIDATE':
    raise SystemExit('No successful focused proof record.')
for lane, record in result['lanes'].items():
    if record['recursive_coqchk']['exit_code'] != 0:
        raise SystemExit('Failed kernel check: ' + lane)
    if record['compile'][-1]['closed_reports'] != 9:
        raise SystemExit('Unexpected exact-interface assumption report count.')
    for module, source in record['files'].items():
        p = root / source['input']
        if hashlib.sha256(p.read_bytes()).hexdigest() != source['input_sha256']:
            raise SystemExit('Compiled input mismatch: ' + module)
        text = p.read_text()
        if result['compat_818']:
            text = text.replace('From Stdlib', 'From Coq')
        if hashlib.sha256(text.encode()).hexdigest() != source['compiled_source_sha256']:
            raise SystemExit('Compatibility source mismatch: ' + module)
    for call in record['compile'] + [record['recursive_coqchk']]:
        log = root / 'verification' / call['log']
        if hashlib.sha256(log.read_bytes()).hexdigest() != call['log_sha256']:
            raise SystemExit('Compiler log mismatch: ' + str(log))
regen = json.loads((root / 'verification/regeneration-portable.json').read_text())
if regen['status'] != 'PASS_REGENERATION_EXACT_DIFF' or regen['unchanged_count'] != 40:
    raise SystemExit('Unexpected regeneration record.')
print('PASS:', len(manifest['files']), 'payload digests; focused proof/source/log bindings; regeneration record.')
print('Integrity and receipt check only; use check.py to rerun the proof kernels.')
