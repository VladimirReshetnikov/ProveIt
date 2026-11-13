#!/usr/bin/env python3
"""Audit fixed compact first-index window without rerunning Lean."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-fixed-compact-index-window-draft'
obs=packet/'observations/attempt01'
out=Path('/tmp/p64-qcube72-fixed-compact-index-window-priority-check01')
pins={packet/'FreeMainFixedCompactIndexWindow.lean':'5f4328358031cdabc3d32a0bb2c34c96c7da7d01b5c95babf7161b06f568674f',
 packet/'check01.py':'1a66f9c231d9d35f5d0280f9177ab2a240d290ae4ad24afd0507b523df1ff11d',
 packet/'missing_child.py':'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
 obs/'compile.log':'83faa9b68bb28d33c165fbbe6a521ba5d62943ccc33361c55980aad8cd6d61a4',
 obs/'result.json':'7ddf5dd4be8fa10295470719ba49cc99a8595673a031cd5290b73b8ea4da72e0',
 out/'FreeMainFixedCompactIndexWindow.olean':'7202be120448b67b446f6af2dcc1bb90de67e9fa7cfc527da35cc73165252d44'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in pins.items():
    if not p.is_file() or p.is_symlink() or sha(p)!=h:raise RuntimeError('artifact mismatch '+str(p))
for n in ('compile.log','result.json'):
    if (out/n).read_bytes()!=(obs/n).read_bytes():raise RuntimeError('terminal copy mismatch '+n)
r=json.loads((obs/'result.json').read_text())
if (r['status'],r['exit'],r['stop_reason'],r['guards_stable'])!=('PASS',0,None,True):raise RuntimeError('failed receipt')
if r['guards_before']!=r['guards_after'] or not r['group_rss_samples']:raise RuntimeError('guard/sample mismatch')
if (r['runner_sha256'],r['missing_child_helper_sha256'],r['log_sha256'],r['object_sha256'])!=(
 pins[packet/'check01.py'],pins[packet/'missing_child.py'],pins[obs/'compile.log'],pins[out/'FreeMainFixedCompactIndexWindow.olean']):raise RuntimeError('receipt hash mismatch')
if (obs/'compile.log').read_text().strip()!="'FreeMainFixedCompactIndexWindow.first_index_window' depends on axioms: [propext, Classical.choice, Quot.sound]":raise RuntimeError('compiler log mismatch')
for name,item in r['guards_after'].items():
    p=Path(name)
    if item is None:
        if p.exists() or p.is_symlink():raise RuntimeError('guarded shadow present '+name)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch '+name)
providers=[
 ('/tmp/p64-qcube72-fixed-compact-first-index-priority-check02/FreeMainFixedCompactFirstIndex.olean',
  'research/p64-qcube72-fixed-compact-first-index-draft/observations/attempt02/result.json',
  '4537bb7943f48bf600027fc7d0c4fab35476a10fa25f8e94d381b5cdecaff20d'),
 ('/tmp/p64-qcube72-half-index-lower-priority-check04/FreeMainHalfIndexLower.olean',
  'research/p64-qcube72-half-index-lower-draft/observations/attempt04/result.json',
  'efd15c9bbd3394fbf085518e4f7374a0e0d75013a771872d6700a542c8ad5839')]
for path,receipt,h in providers:
    if r['guards_after'][path]['sha256']!=h:raise RuntimeError('provider mismatch '+path)
    p=json.loads((root/receipt).read_text())
    if (p['status'],p['exit'],p['object_sha256'])!=('PASS',0,h):raise RuntimeError('producer mismatch '+receipt)
s=(packet/'FreeMainFixedCompactIndexWindow.lean').read_text()
for x in ('∃ n : V, n<R ∧ R<2*n ∧',
          'xcoord n (2*(P-1)+1)=v 9 ∧ 2*ycoord n (2*(P-1)+1)=k',
          'obtain ⟨n,hnlt,hnx,hny⟩ := FreeMainFixedCompactFirstIndex.first_index_lt_rank K v hv hz',
          'FreeMainFixedCompactRankedMain.fixed_main_at_rank K v hv hz',
          'FreeMainHalfIndexLower.main_lt_twice_first X Y (v 10) (v 11) n R (hv 11) hny hmy',
          'exact ⟨n,hnlt,htwice,hnx,hny⟩'):
    if x not in s:raise RuntimeError('theorem scope or witness flow changed '+x)
print(json.dumps({'status':'PASS','lean_replayed':False,'guards_checked':len(r['guards_after']),
 'direct_producer_receipts':2,'scope':'same model n satisfies n<R<2n at fixed symbolic compact ports; inherited ancestry'},sort_keys=True))
