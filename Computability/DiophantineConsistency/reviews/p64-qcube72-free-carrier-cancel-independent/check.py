#!/usr/bin/env python3
"""Audit generic free-carrier cancellation without Lean replay."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-free-carrier-cancel-draft'
obs=packet/'observations/attempt01'
out=Path('/tmp/p64-qcube72-free-carrier-cancel-priority-check01')
pins={packet/'FreeMainCarrierCancel.lean':'f3ebf63fcf2ecf26936d8394ee74bc578937752223e4a6753da236d1784c99d0',
 packet/'check01.py':'6fd3cf9dc29294c90b46bfc67e596ec526fb904a8f8fd87d78ff5f3f0ae717ab',
 packet/'missing_child.py':'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
 obs/'compile.log':'ae4e9a7b0e23b456811531eb93c2d18bf11be8989b0e7d0b4a8a16b3641f30df',
 obs/'result.json':'50de53e9add381bc15c72821307b143984f1b191c1ce51ee347dda6b4ac3b9ef',
 out/'FreeMainCarrierCancel.olean':'e43083918e775c396704e341db1268495c369a7d7b9b7f01fc207adb90775ef1'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in pins.items():
    if not p.is_file() or p.is_symlink() or sha(p)!=h:raise RuntimeError('artifact mismatch '+str(p))
for n in ('compile.log','result.json'):
    if (out/n).read_bytes()!=(obs/n).read_bytes():raise RuntimeError('terminal copy mismatch '+n)
r=json.loads((obs/'result.json').read_text())
if (r['status'],r['exit'],r['stop_reason'],r['guards_stable'])!=('PASS',0,None,True):raise RuntimeError('failed receipt')
if r['guards_before']!=r['guards_after'] or not r['group_rss_samples']:raise RuntimeError('guard/sample mismatch')
if (r['runner_sha256'],r['missing_child_helper_sha256'],r['log_sha256'],r['object_sha256'])!=(
 pins[packet/'check01.py'],pins[packet/'missing_child.py'],pins[obs/'compile.log'],pins[out/'FreeMainCarrierCancel.olean']):raise RuntimeError('receipt hash mismatch')
if (obs/'compile.log').read_text().strip()!="'FreeMainCarrierCancel.cancel' depends on axioms: [propext, Classical.choice, Quot.sound]":raise RuntimeError('compiler log mismatch')
for name,item in r['guards_after'].items():
    p=Path(name)
    if item is None:
        if p.exists() or p.is_symlink():raise RuntimeError('guarded shadow present '+name)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch '+name)
provider='/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/Compact44/P64Early.olean'
if r['guards_after'][provider]['sha256']!='9f9f46d3c82a74024d2e550df1074c3dc706c6242eb55235fa6bcc43d01341c2':
    raise RuntimeError('captured provider mismatch')
s=(packet/'FreeMainCarrierCancel.lean').read_text()
for x in ('(hq3 : 3≤q) (hy0 : 0<y0) (hY : Y=q*(q*q)*y0)',
          '(hcar : (Y*Y)*g=(Y*Y)*(X+(X*Y+Y)*c)+(4*(X*Y+Y)+3)*h)',
          '∃ e mu : V, 0<e ∧ Y*Y=e*mu ∧ e∣9 ∧ 0<mu ∧',
          'q*(q*(q*q))≤mu ∧ mu∣h', 'gcd_cancel U H h 0 hU0 hmod',
          'gcd_dvd_nine X Y e heY heH\''):
    if x not in s:raise RuntimeError('theorem or witness flow changed '+x)
print(json.dumps({'status':'PASS','lean_replayed':False,'guards_checked':len(r['guards_after']),
 'scope':'generic model free-carrier cancellation under explicit q-cube and carrier assumptions; captured ancestry'},sort_keys=True))
