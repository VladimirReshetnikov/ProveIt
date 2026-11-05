#!/usr/bin/env python3
"""Audit the actual-zero first Pell index extraction without Lean replay."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-first-index-extraction-draft'
obs=packet/'observations/attempt01'
out=Path('/tmp/p64-qcube72-first-index-extraction-priority-check01')
pins={packet/'FreeMainFirstIndexExtraction.lean':'58f91276267968ffe93169fbb225387a3e0b26bf7ddf1a1177c3744ce872c9ba',
 packet/'check01.py':'ac4a74356124f1a9c3c859f62f55ecffc56510efe56ee9355fbf813df5ef45df',
 packet/'missing_child.py':'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
 obs/'compile.log':'17db198d332551177d2b7e70fdd5cc916608b4a2d64cc6eb231f178e0c55deff',
 obs/'result.json':'3bfcae3d84fff56e41529b64a8330b0548e6a8073b7c1cc12ac06d13b9b4b622',
 out/'FreeMainFirstIndexExtraction.olean':'67ed132545d507e96b24bf023cf91a51c6b5623902889bc36daaa55ad39ad785'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in pins.items():
    if not p.is_file() or p.is_symlink() or sha(p)!=h: raise RuntimeError('artifact mismatch '+str(p))
for n in ('compile.log','result.json'):
    if (out/n).read_bytes()!=(obs/n).read_bytes():raise RuntimeError('terminal copy mismatch '+n)
r=json.loads((obs/'result.json').read_text())
if (r['status'],r['exit'],r['stop_reason'],r['guards_stable'])!=('PASS',0,None,True):raise RuntimeError('failed receipt')
if r['guards_before']!=r['guards_after'] or not r['group_rss_samples']:raise RuntimeError('guard/sample mismatch')
if (r['runner_sha256'],r['missing_child_helper_sha256'],r['log_sha256'],r['object_sha256'])!=(
 pins[packet/'check01.py'],pins[packet/'missing_child.py'],pins[obs/'compile.log'],pins[out/'FreeMainFirstIndexExtraction.olean']):raise RuntimeError('receipt hash mismatch')
if (obs/'compile.log').read_text().strip()!="'FreeMainFirstIndexExtraction.first_index' depends on axioms: [propext, Classical.choice, Quot.sound]":
    raise RuntimeError('unexpected compiler log')
for name,item in r['guards_after'].items():
    p=Path(name)
    if item is None:
        if p.exists() or p.is_symlink():raise RuntimeError('guarded shadow present '+name)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch '+name)
providers={
 '/tmp/p64-qcube72-residuals-priority-check01/FreeMainGraphResiduals.olean':'3c25b31eb0baa9aa8c9148d75da59af554978371b6b3a9eea5bf7dea51a73720',
 '/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/ArithmeticPellFirstNorm.olean':'82b45a6e4da9ab538940849ebb6515056e82a20fb7f57a353441a90f50438854'}
for path,h in providers.items():
    if r['guards_after'][path]['sha256']!=h:raise RuntimeError('provider mismatch '+path)
producer=json.loads((root/'research/p64-qcube72-residuals-draft/observations/attempt01/result.json').read_text())
if (producer['status'],producer['exit'],producer['object_sha256'])!=('PASS',0,providers[next(iter(providers))]):raise RuntimeError('residual provider receipt mismatch')
s=(packet/'FreeMainFirstIndexExtraction.lean').read_text()
for x in ('(hv : ∀ i,0<v i)', '(hz : InternalZero (P64QCube72Free.graph',
          '∃ n : V, n≤k ∧ xcoord n (2*(P-1)+1)=v 9 ∧',
          '2*ycoord n (2*(P-1)+1)=k', 'FreeMainGraphResiduals.residuals p v hv hz',
          'positive_parameter_solution P (v 9) k hP hnorm'):
    if x not in s:raise RuntimeError('theorem scope changed '+x)
print(json.dumps({'status':'PASS','lean_replayed':False,'guards_checked':len(r['guards_after']),
                  'scope':'actual positive 72-zero; captured first-norm provider and inherited ancestry'},sort_keys=True))
