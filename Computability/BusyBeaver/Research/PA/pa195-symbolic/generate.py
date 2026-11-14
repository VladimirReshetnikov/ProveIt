#!/usr/bin/env python3
"""Generate Lean symbolic-contract batches from an explicit source-site JSON.

The generated Lean theorems run the upstream executor on every supplied case.
This generator does not prove that the JSON is the compiled source program.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parents[5]
DEFAULT_ARCHIVE = ROOT / 'docs/incoming/pa195_conpa_2026-11-13.zip'
DEFAULT_MEMBER = 'pa195_conpa/pa195/source.json'
DEFAULT_HASH = 'd35c2d718f07dd80892f42e0b78f9e6a21f05aa0521cdc779a7dadade502df69'
PHYSICAL = [6, 2, 0, 4, 3, 7, 8, 5, 1]

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--out', type=Path, required=True)
p.add_argument('--archive', type=Path, default=DEFAULT_ARCHIVE)
p.add_argument('--member', default=DEFAULT_MEMBER)
p.add_argument('--sha256', default=DEFAULT_HASH)
p.add_argument('--engine-module', default='PA195RuntimeEngine')
p.add_argument('--machine', default='PA195RuntimeEngine.machine')
p.add_argument('--start-site', type=int, default=0)
p.add_argument('--stop-site', type=int)
p.add_argument('--batch-size', type=int, default=10)
a = p.parse_args()
for name in (a.engine_module, a.machine):
    if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', name):
        raise SystemExit(f'invalid Lean name: {name}')
with ZipFile(a.archive) as z:
    payload = z.read(a.member)
if hashlib.sha256(payload).hexdigest() != a.sha256:
    raise SystemExit('source-site JSON SHA-256 mismatch')
sites = json.loads(payload)
if any(s['ordinal'] != i for i, s in enumerate(sites)):
    raise SystemExit('source-site ordinals are not contiguous')
if len({s['path'] for s in sites}) != len(sites):
    raise SystemExit('source paths are not unique')
for s in sites:
    if any(x not in '01' for x in s['path']) or len(s['path']) > 48:
        raise SystemExit('invalid source path')
stop = len(sites) if a.stop_site is None else a.stop_site
if not (0 <= a.start_site <= stop <= len(sites) and a.batch_size > 0):
    raise SystemExit('invalid site range or batch size')

def bits(path):
    return '[' + ', '.join('true' if b == '1' else 'false' for b in path) + ']'

def frame(i, extra=0, effect='.none'):
    if not 0 <= i < len(sites):
        raise SystemExit(f'invalid successor {i}')
    return f'frame {bits(sites[i]["path"])} {extra} ({effect})'

def cases_for(item):
    i = item['ordinal']
    instruction = item['instruction']
    op = instruction[0]
    st = frame(i)
    if op == 'dec':
        _, r, zero, positive = instruction
        if r not in range(len(PHYSICAL)):
            raise SystemExit(f'invalid register at site {i}')
        pr = PHYSICAL[r]
        return [f'⟨some ({pr}, true), {st}, some ({frame(zero)})⟩',
                f'⟨some ({pr}, false), {st}, some ({frame(positive, 1, f".dec {pr}")})⟩']
    if op == 'inc':
        _, r, successor = instruction
        if r not in range(len(PHYSICAL)):
            raise SystemExit(f'invalid register at site {i}')
        return [f'⟨none, {st}, some ({frame(successor, 0, f".inc {PHYSICAL[r]}")})⟩']
    if op == 'jump':
        _, successor = instruction
        return [f'⟨none, {st}, some ({frame(successor)})⟩']
    if op == 'halt' and len(instruction) == 1:
        return [f'⟨none, {st}, none⟩']
    raise SystemExit(f'unknown instruction at site {i}: {instruction!r}')

a.out.mkdir(parents=True, exist_ok=True)
manifest = []
for first in range(a.start_site, stop, a.batch_size):
    last = min(first + a.batch_size, stop)
    batch = []
    for item in sites[first:last]:
        for index, c in enumerate(cases_for(item)):
            batch.append(f'  -- site {item["ordinal"]}, outcome {index}\n  {c}')
    module = f'PA195SymbolicBatch{first:04d}_{last:04d}'
    content = f'''import PA195Symbolic
import {a.engine_module}
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace {module}
open M6.Zip M6.Runtime PA195Symbolic

def cases : List Contract := [
''' + ',\n'.join(batch) + f'''
]

theorem verified : cases.all (accepted {a.machine}) = true := by decide +kernel
#print axioms verified
end {module}
'''
    path = a.out / f'{module}.lean'
    path.write_text(content)
    manifest.append({'module': module, 'first_site': first, 'last_site_exclusive': last,
                     'contracts': len(batch), 'sha256': hashlib.sha256(content.encode()).hexdigest()})
(a.out / 'manifest.json').write_text(json.dumps({'source_sha256': a.sha256, 'batches': manifest}, indent=2) + '\n')
print(f'Generated {len(manifest)} batches, {sum(b["contracts"] for b in manifest)} contracts, sites {a.start_site}..{stop - 1}')
