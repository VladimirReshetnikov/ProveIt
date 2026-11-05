#!/usr/bin/env python3
"""Audit the conditional same-witness no-gamma theorem without Lean replay."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-divisible-q-no-old-gamma-draft'
obs=packet/'observations/attempt02'
out=Path('/tmp/p64-qcube72-divisible-q-no-old-gamma-priority-check02')
pins={packet/'FreeMainDivisibleQNoOldGamma.lean':'c986b3c588a74730991681805d906e611435915fb54fd81128a4e67779720564',
 packet/'check02.py':'d8cd1436fda76ce8517ce1a43bddd86c756695d6e3d62aabbbee6986eec94f66',
 packet/'missing_child.py':'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
 obs/'compile.log':'b066d7f7b1858fb4d950aff4384fb978b720337c1738a0c067b3bac3c6aa2c32',
 obs/'result.json':'e3086bb59b11ea022391c038dbc04275045f8aad9bf9f9eb8fbf87ab5f7edbe4',
 out/'FreeMainDivisibleQNoOldGamma.olean':'80d54d2773c0baf82ccadaffef7b2dc70ce551a28d91f6ca53f7ea81d949a528'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in pins.items():
    if not p.is_file() or p.is_symlink() or sha(p)!=h:raise RuntimeError('artifact mismatch '+str(p))
for n in ('compile.log','result.json'):
    if (out/n).read_bytes()!=(obs/n).read_bytes():raise RuntimeError('terminal copy mismatch '+n)
r=json.loads((obs/'result.json').read_text())
if (r['status'],r['exit'],r['stop_reason'],r['guards_stable'])!=('PASS',0,None,True):raise RuntimeError('failed receipt')
if r['guards_before']!=r['guards_after'] or not r['group_rss_samples']:raise RuntimeError('guard/sample mismatch')
if (r['runner_sha256'],r['missing_child_helper_sha256'],r['log_sha256'],r['object_sha256'])!=(
 pins[packet/'check02.py'],pins[packet/'missing_child.py'],pins[obs/'compile.log'],pins[out/'FreeMainDivisibleQNoOldGamma.olean']):raise RuntimeError('receipt hash mismatch')
names=('carrier_forces_dvd','fixed_no_gamma')
want='\n'.join(f"'FreeMainDivisibleQNoOldGamma.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names)
if (obs/'compile.log').read_text().strip()!=want:raise RuntimeError('compiler log mismatch')
for name,item in r['guards_after'].items():
    p=Path(name)
    if item is None:
        if p.exists() or p.is_symlink():raise RuntimeError('guarded shadow present '+name)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch '+name)
providers=[
 ('/tmp/p64-qcube72-conditional-old-carrier-priority-check02/FreeMainConditionalOldCarrier.olean',
  'research/p64-qcube72-conditional-old-carrier-draft/observations/attempt02/result.json',
  'cf77a2a51742d9dc22e20d2e766df715d4318557848602bb2790466feb82fa2e'),
 ('/tmp/p64-qcube72-actual-divisible-q-obstruction-priority-check01/FreeMainActualDivisibleQObstruction.olean',
  'research/p64-qcube72-actual-divisible-q-obstruction-draft/observations/attempt01/result.json',
  'bf804a8acde053c241f8a45faa73386ce7148d48c69fe78c7fb6f75c9a421bfe')]
for path,receipt,h in providers:
    if r['guards_after'][path]['sha256']!=h:raise RuntimeError('provider mismatch '+path)
    p=json.loads((root/receipt).read_text())
    if (p['status'],p['exit'],p['object_sha256'])!=('PASS',0,h):raise RuntimeError('producer mismatch '+receipt)
s=(packet/'FreeMainDivisibleQNoOldGamma.lean').read_text()
for x in ('(hU : 0<U)', '(hn : 2*n=R+1) (hks : k=2*n+4*(X*U)*s)',
          '(hold : h+k=U*gamma+(R+1)) : U∣h',
          '(h3 : (3:V)∣(compactPorts K 0:V)*v 0+1)',
          '¬ ∃ gamma : V, v 13+k=(Y*Y)*gamma+(R+1)',
          'FreeMainActualDivisibleQObstruction.fixed_zero K v hv hz h3',
          'FreeMainConditionalOldCarrier.fixed_of_witness K v gamma hv hz hold',
          'carrier_forces_dvd (Y*Y) X R n k (v 13) gamma s hU hn hks\' hold'):
    if x not in s:raise RuntimeError('hypothesis or witness flow changed '+x)
print(json.dumps({'status':'PASS','lean_replayed':False,'guards_checked':len(r['guards_after']),
 'direct_producer_receipts':2,'scope':'fixed positive zero and 3|q exclude same-witness old carrier gamma only; inherited ancestry'},sort_keys=True))
