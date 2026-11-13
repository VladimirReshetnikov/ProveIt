#!/usr/bin/env python3
"""Audit the generic 3-divisibility obstruction without Lean replay."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-divisible-q-obstruction-draft'
obs=packet/'observations/attempt02'
out=Path('/tmp/p64-qcube72-divisible-q-obstruction-priority-check02')
pins={packet/'FreeMainDivisibleQObstruction.lean':'7e19722acface5914c82b8fb2ff2c7339e4dfd6f62ce06060aa75fc8d0358aad',
 packet/'check02.py':'d3811cd65713592949eef5e9075adb2b69a6e1677d29d3b98fe92a4afcb998a3',
 packet/'missing_child.py':'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
 obs/'compile.log':'4ea8de6fee328c05237e2077e587bab6e42678fb0e25ca643176677f96e61df4',
 obs/'result.json':'2bdaf6a476857e0679a055e8c88558fcc6a1a13366a56de30758af0464c80e22',
 out/'FreeMainDivisibleQObstruction.olean':'f8ed9da0c9bbce5cbd049cd928f6c342b13f04ef90275b8e6668741d7932f30b'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in pins.items():
    if not p.is_file() or p.is_symlink() or sha(p)!=h:raise RuntimeError('artifact mismatch '+str(p))
for n in ('compile.log','result.json'):
    if (out/n).read_bytes()!=(obs/n).read_bytes():raise RuntimeError('terminal copy mismatch '+n)
r=json.loads((obs/'result.json').read_text())
if (r['status'],r['exit'],r['stop_reason'],r['guards_stable'])!=('PASS',0,None,True):raise RuntimeError('failed receipt')
if r['guards_before']!=r['guards_after'] or not r['group_rss_samples']:raise RuntimeError('guard/sample mismatch')
if (r['runner_sha256'],r['missing_child_helper_sha256'],r['log_sha256'],r['object_sha256'])!=(
 pins[packet/'check02.py'],pins[packet/'missing_child.py'],pins[obs/'compile.log'],pins[out/'FreeMainDivisibleQObstruction.olean']):raise RuntimeError('receipt hash mismatch')
if (obs/'compile.log').read_text().strip()!="'FreeMainDivisibleQObstruction.not_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]":raise RuntimeError('compiler log mismatch')
for name,item in r['guards_after'].items():
    p=Path(name)
    if item is None:
        if p.exists() or p.is_symlink():raise RuntimeError('guarded shadow present '+name)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch '+name)
provider='/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/ArithmeticPellRecurrence.olean'
if r['guards_after'][provider]['sha256']!='d87f772441f0309bf879aeef7673bbdc2d2367d016402bafc8e6763e96b62a39':raise RuntimeError('captured provider mismatch')
s=(packet/'FreeMainDivisibleQObstruction.lean').read_text()
for x in ('(hq3 : (3:V)∣q) (hU : 0<U)', 'g*g=1+delta a*c*c)',
          'U*g=U*(X+a*c)+H*h) : ¬U∣h',
          'have hx3 : (3:V)∣X', 'have hD3 : delta a=3*',
          'have hg : g=X+a*c+H*t', 'have hg3 : (3:V)∣g',
          'congrArg (fun z : V => z%3) he'):
    if x not in s:raise RuntimeError('hypothesis or proof flow changed '+x)
print(json.dumps({'status':'PASS','lean_replayed':False,'guards_checked':len(r['guards_after']),
 'scope':'3 divides q plus positive U, explicit main norm and free carrier; captured ancestry'},sort_keys=True))
