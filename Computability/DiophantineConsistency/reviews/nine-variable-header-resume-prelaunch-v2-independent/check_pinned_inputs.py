#!/usr/bin/env python3
"""Read-only verification of the six declared pins and 1,212 source files."""
import hashlib
import json
from pathlib import Path
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('run with python3 -I -S -B')
research=Path(__file__).resolve().parents[2]/'research'
repo=next(p for p in research.parents if (p/'lakefile.toml').is_file())
pins={
 research/'nine-variable-external-matrix-preflight/header-result.json':'7c5751dfd7002b3425e71f462f8058078ee0911e5f4ecbcd1e66871a4832b9fe',
 research/'nine-variable-current-base-source-survey/result-final.json':'7aa788ec612ef2d1cf40e65cf16b507099532477cd581dfe2c560d7b934d31ca',
 research/'nine-variable-external-matrix-preflight/policy.json':'d4c513bcd322b6c2e67a6611d47a69cbd195191f6c7d9a4ea37a210471b57db9',
 research/'compiled-header-inventory/inventory.py':'88ebe1423c4bb4237ba2a7ce2b3e5f8fd4df807c151a8ce976075dbdf5938987',
 research/'compiled-header-inventory/stream_imports.lean':'04c6de3745c83024184666577f5ee8d2d166ed54036544bef2e079de2601da63',
 Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'):'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in pins.items():
    if not p.is_file() or sha(p)!=h:raise RuntimeError('input pin mismatch: '+str(p))
survey=json.loads((research/'nine-variable-current-base-source-survey/result-final.json').read_text())
for module,rec in survey['project_sources'].items():
    p=repo/rec['source']
    if not p.is_file() or sha(p)!=rec['source_sha256']:raise RuntimeError('source drift: '+module)
assert len(survey['project_sources'])==1212
assert len(survey['declared_external'])==len(set(survey['declared_external']))==128
print(json.dumps({'status':'PASS_PINNED_INPUTS','declared_external_seeds':128,
 'pinned_project_sources':1212,'other_input_pins':len(pins),
 'scope':'Read-only byte hashes, not project compilation, header traversal or dynamic provider provenance.'},sort_keys=True))
