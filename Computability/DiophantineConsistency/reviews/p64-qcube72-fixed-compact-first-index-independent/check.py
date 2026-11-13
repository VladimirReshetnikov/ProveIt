#!/usr/bin/env python3
"""Audit fixed compact first-index composition without Lean replay."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-fixed-compact-first-index-draft'
obs=packet/'observations/attempt02'
out=Path('/tmp/p64-qcube72-fixed-compact-first-index-priority-check02')
pins={packet/'FreeMainFixedCompactFirstIndex.lean':'8531fb5512662c7a13a11b840599179bf9f2a1bd5920dfb1d6cbc41ed447e113',
 packet/'check02.py':'de6c3d94cd5b9e80d5311397acc7289e147c93b198442e14ee9097550fbe090e',
 packet/'missing_child.py':'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
 obs/'compile.log':'1ca00bbcdb188bad64f0168425469c3c3d2c447a6cb1340a90e9ebba1c481f35',
 obs/'result.json':'a7e800847d346e5bfb9462973f4012e428de85ff205fed0c19bd26f6f380930d',
 out/'FreeMainFixedCompactFirstIndex.olean':'4537bb7943f48bf600027fc7d0c4fab35476a10fa25f8e94d381b5cdecaff20d'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in pins.items():
    if not p.is_file() or p.is_symlink() or sha(p)!=h:raise RuntimeError('artifact mismatch '+str(p))
for n in ('compile.log','result.json'):
    if (out/n).read_bytes()!=(obs/n).read_bytes():raise RuntimeError('terminal copy mismatch '+n)
r=json.loads((obs/'result.json').read_text())
if (r['status'],r['exit'],r['stop_reason'],r['guards_stable'])!=('PASS',0,None,True):raise RuntimeError('failed receipt')
if r['guards_before']!=r['guards_after'] or not r['group_rss_samples']:raise RuntimeError('guard/sample mismatch')
if (r['runner_sha256'],r['missing_child_helper_sha256'],r['log_sha256'],r['object_sha256'])!=(
 pins[packet/'check02.py'],pins[packet/'missing_child.py'],pins[obs/'compile.log'],pins[out/'FreeMainFixedCompactFirstIndex.olean']):raise RuntimeError('receipt hash mismatch')
if (obs/'compile.log').read_text().strip()!="'FreeMainFixedCompactFirstIndex.first_index_lt_rank' depends on axioms: [propext, Classical.choice, Quot.sound]":raise RuntimeError('compiler log mismatch')
for name,item in r['guards_after'].items():
    p=Path(name)
    if item is None:
        if p.exists() or p.is_symlink():raise RuntimeError('guarded shadow present '+name)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch '+name)
providers=[
 ('/tmp/p64-qcube72-fixed-compact-ranked-main-check01/FreeMainFixedCompactRankedMain.olean',
  'research/p64-qcube72-fixed-compact-ranked-main-draft/observations/attempt01/result.json',
  'eb8fbc81679bd6193c8879510c34e1263f8baef31a079abb0c3226ce449f4079'),
 ('/tmp/p64-qcube72-first-index-extraction-priority-check01/FreeMainFirstIndexExtraction.olean',
  'research/p64-qcube72-first-index-extraction-draft/observations/attempt01/result.json',
  '67ed132545d507e96b24bf023cf91a51c6b5623902889bc36daaa55ad39ad785'),
 ('/tmp/p64-qcube72-first-index-comparison-priority-check02/FreeMainFirstIndexComparison.olean',
  'research/p64-qcube72-first-index-comparison-draft/observations/attempt02/result.json',
  'b047e0649391b7f65d2b2ec83d4f8fda46566adcc22abf8bd38f4bd566a3f6d6')]
for path,receipt,h in providers:
    if r['guards_after'][path]['sha256']!=h:raise RuntimeError('provider mismatch '+path)
    p=json.loads((root/receipt).read_text())
    if (p['status'],p['exit'],p['object_sha256'])!=('PASS',0,h):raise RuntimeError('producer mismatch '+receipt)
s=(packet/'FreeMainFixedCompactFirstIndex.lean').read_text()
for x in ('(hv : ∀ i,0<v i)', '(hz : InternalZero (P64QCube72Free.graph',
          '∃ n : V, n<FreeMainAuxNorm.rank p v ∧',
          'xcoord n (2*(P-1)+1)=v 9 ∧ 2*ycoord n (2*(P-1)+1)=k',
          'FreeMainFirstIndexExtraction.first_index p v hv hz',
          'FreeMainFixedCompactRankedMain.fixed_main_at_rank K v hv hz',
          'FreeMainFirstIndexComparison.first_lt_main X Y k (v 10) n R'):
    if x not in s:raise RuntimeError('theorem scope changed '+x)
print(json.dumps({'status':'PASS','lean_replayed':False,'guards_checked':len(r['guards_after']),
 'direct_producer_receipts':3,'scope':'actual zero at fixed compact symbolic ports; inherited provider ancestry'},sort_keys=True))
