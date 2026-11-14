#!/usr/bin/env python3
"""Generate Lean ordinal/instruction claims from the pinned PA195 site list."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[5]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--out', required=True, type=Path)
p.add_argument('--start-site', type=int, default=0)
p.add_argument('--stop-site', type=int)
p.add_argument('--batch-size', type=int, default=100)
a = p.parse_args()
sys.path.insert(0, str(root / 'Computability/BusyBeaver/Research/PA'))
from packet_inputs import PlacedPacket
with PlacedPacket(root, '195') as z:
    payload = z.read('pa195_conpa/pa195/source.json')
if hashlib.sha256(payload).hexdigest() != 'd35c2d718f07dd80892f42e0b78f9e6a21f05aa0521cdc779a7dadade502df69':
    raise SystemExit('source-site JSON SHA-256 mismatch')
sites = json.loads(payload)
if len(sites) != 3700 or any(s['ordinal'] != i for i, s in enumerate(sites)):
    raise SystemExit('unexpected source-site count or ordinal order')
stop = len(sites) if a.stop_site is None else a.stop_site
if not (0 <= a.start_site <= stop <= len(sites) and a.batch_size > 0):
    raise SystemExit('invalid site range or batch size')

def bits(path):
    if any(b not in '01' for b in path):
        raise ValueError('invalid path')
    return '[' + ', '.join('true' if b == '1' else 'false' for b in path) + ']'

def operation(s):
    name, arg = s['op'], s['arg']
    if name == 'halt':
        return '.halt'
    if name not in ('inc', 'dec', 'breakTo', 'continueTo') or not isinstance(arg, int) or arg < 0:
        raise ValueError('invalid operation')
    return f'.{name} {arg}'

def instruction(s):
    value = s['instruction']
    name = value[0]
    if name == 'inc' and len(value) == 3:
        return f'.inc {value[1]} (some {value[2]})'
    if name == 'dec' and len(value) == 4:
        return f'.dec {value[1]} (some {value[2]}) (some {value[3]})'
    if name == 'jump' and len(value) == 2:
        return f'.jump (some {value[1]})'
    if name == 'halt' and len(value) == 1:
        return '.halt'
    raise ValueError('invalid instruction')

a.out.mkdir(parents=True, exist_ok=True)
manifest = []
for first in range(a.start_site, stop, a.batch_size):
    last = min(first + a.batch_size, stop)
    module = f'PA195SourceBatch{first:04d}_{last:04d}'
    entries = [f'  ⟨{s["ordinal"]}, ⟨{bits(s["path"])}, {operation(s)}⟩, {instruction(s)}⟩'
               for s in sites[first:last]]
    content = f'''import PA195SourceClaims
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace {module}
open M6.Source PA195SourceClaims

def claims : List Claim := [
''' + ',\n'.join(entries) + f'''
]

theorem verified : claims.all accepted = true := by decide +kernel
#print axioms verified
end {module}
'''
    (a.out / f'{module}.lean').write_text(content)
    manifest.append({'module': module, 'first_site': first, 'last_site_exclusive': last,
                     'claims': len(entries), 'sha256': hashlib.sha256(content.encode()).hexdigest()})
(a.out / 'manifest.json').write_text(json.dumps({'batches': manifest}, indent=2) + '\n')
print(f'Generated {len(manifest)} batches, {sum(b["claims"] for b in manifest)} source-site claims, sites {a.start_site}..{stop - 1}')
