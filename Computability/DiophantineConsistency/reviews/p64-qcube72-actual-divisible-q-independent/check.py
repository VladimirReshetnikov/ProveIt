#!/usr/bin/env python3
"""Audit actual-zero 3-divisibility client without Lean replay."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-actual-divisible-q-obstruction-draft'
obs=packet/'observations/attempt01'
out=Path('/tmp/p64-qcube72-actual-divisible-q-obstruction-priority-check01')
pins={packet/'FreeMainActualDivisibleQObstruction.lean':'6e186ef99bc68076c9e9bc1e3c57c9999bf15f754dbf8731e2e60a4c7e8297ce',
 packet/'check01.py':'33add9b4ccecf3a2b97daa4c5bfbad5c28b3e75d04fe5fc6b2fa5ef307566a0d',
 packet/'missing_child.py':'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
 obs/'compile.log':'c67b56a266f91712d4d50f1ba6d3c7a36d3f452ef39d695d6036447f28259837',
 obs/'result.json':'828af6073480d5bf4f2b0a4611629a0c2cd9138c36a5b5a4dcd243e80717658c',
 out/'FreeMainActualDivisibleQObstruction.olean':'bf804a8acde053c241f8a45faa73386ce7148d48c69fe78c7fb6f75c9a421bfe'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in pins.items():
    if not p.is_file() or p.is_symlink() or sha(p)!=h:raise RuntimeError('artifact mismatch '+str(p))
for n in ('compile.log','result.json'):
    if (out/n).read_bytes()!=(obs/n).read_bytes():raise RuntimeError('terminal copy mismatch '+n)
r=json.loads((obs/'result.json').read_text())
if (r['status'],r['exit'],r['stop_reason'],r['guards_stable'])!=('PASS',0,None,True):raise RuntimeError('failed receipt')
if r['guards_before']!=r['guards_after'] or not r['group_rss_samples']:raise RuntimeError('guard/sample mismatch')
if (r['runner_sha256'],r['missing_child_helper_sha256'],r['log_sha256'],r['object_sha256'])!=(
 pins[packet/'check01.py'],pins[packet/'missing_child.py'],pins[obs/'compile.log'],pins[out/'FreeMainActualDivisibleQObstruction.olean']):raise RuntimeError('receipt hash mismatch')
names=('actual_zero','fixed_zero')
want='\n'.join(f"'FreeMainActualDivisibleQObstruction.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names)
if (obs/'compile.log').read_text().strip()!=want:raise RuntimeError('compiler log mismatch')
for name,item in r['guards_after'].items():
    p=Path(name)
    if item is None:
        if p.exists() or p.is_symlink():raise RuntimeError('guarded shadow present '+name)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch '+name)
providers=[
 ('/tmp/p64-qcube72-fixed-compact-carrier-cancel-priority-check01/FreeMainFixedCompactCarrierCancel.olean',
  'research/p64-qcube72-fixed-compact-carrier-cancel-draft/observations/attempt01/result.json',
  '3dbbbc7253c3c0976f39adf9450d35e8b3280e098641c330268d7a9573b69434'),
 ('/tmp/p64-qcube72-divisible-q-obstruction-priority-check02/FreeMainDivisibleQObstruction.olean',
  'research/p64-qcube72-divisible-q-obstruction-draft/observations/attempt02/result.json',
  'f8ed9da0c9bbce5cbd049cd928f6c342b13f04ef90275b8e6668741d7932f30b'),
 ('/tmp/p64-qcube72-main-root-priority-check01/FreeMainGraphMainRoot.olean',
  'research/p64-qcube72-main-root-draft/observations/attempt01/result.json',
  '2429ba1307bde7a83ca68110773cd073825ba5f1d1ee0e1dd59dbbf8dc8d7930')]
for path,receipt,h in providers:
    if r['guards_after'][path]['sha256']!=h:raise RuntimeError('provider mismatch '+path)
    p=json.loads((root/receipt).read_text())
    if (p['status'],p['exit'],p['object_sha256'])!=('PASS',0,h):raise RuntimeError('producer mismatch '+receipt)
s=(packet/'FreeMainActualDivisibleQObstruction.lean').read_text()
for x in ('theorem actual_zero (p : Fin 4 → ℕ)',
          '(h3 : (3:V)∣(p 0:V)*v 0+1)',
          '¬(Y*Y∣v 13)', 'FreeMainGraphMainRoot.main_index p v hv hz',
          'FreeMainDivisibleQObstruction.not_dvd q (v 8) (v 7) U g c (v 13)',
          'theorem fixed_zero (K : ℕ)', '(h3 : (3:V)∣(compactPorts K 0:V)*v 0+1)',
          'actual_zero (compactPorts K) v hv hz h3'):
    if x not in s:raise RuntimeError('source scope or proof flow changed '+x)
print(json.dumps({'status':'PASS','lean_replayed':False,'guards_checked':len(r['guards_after']),
 'direct_producer_receipts':3,'scope':'actual zero plus explicit 3|q, arbitrary and fixed ports; inherited ancestry'},sort_keys=True))
