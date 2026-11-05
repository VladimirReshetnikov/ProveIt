#!/usr/bin/env python3
"""Review terminal 72-zero rank-bridge artifacts without invoking Lean."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-window-ranked-main-bridge-draft'
obs=packet/'observations/attempt02'
out=Path('/tmp/p64-qcube72-window-ranked-main-priority-check02')
expected={
 packet/'FreeMainWindowRankedMain.lean':'3afeff3cacbb6180ae1040d2daff8dce7aad5da9394f7793e0f8cc4260195d50',
 packet/'check02.py':'8937be88a55685d5d0daabbc2910291e509cfa95554fa60b24457db4cee4ac98',
 packet/'missing_child.py':'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
 obs/'compile.log':'63c69af174a16cdb1607bb0ad986fdb203647fd1bb956d9d3e8cf11db30f720a',
 obs/'result.json':'e033c36e8ad94966f9a22abe2f442f13bf3627495d15b16740b13df271ffbc8a',
 out/'FreeMainWindowRankedMain.olean':'3597c62070070a2cc761b9c5a182de486f7ae04a71f139aadc45cad09513db15'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in expected.items():
    if not p.is_file() or p.is_symlink() or sha(p)!=h: raise RuntimeError('artifact mismatch '+str(p))
for name in ('compile.log','result.json'):
    if (out/name).read_bytes()!=(obs/name).read_bytes(): raise RuntimeError('terminal copy mismatch '+name)
r=json.loads((obs/'result.json').read_text())
if (r['status'],r['exit'],r['stop_reason'],r['guards_stable'])!=('PASS',0,None,True): raise RuntimeError('not a successful run')
if r['guards_before']!=r['guards_after'] or not r['group_rss_samples']: raise RuntimeError('guard/sample failure')
if (r['runner_sha256'],r['missing_child_helper_sha256'],r['log_sha256'],r['object_sha256']) != (
 expected[packet/'check02.py'],expected[packet/'missing_child.py'],expected[obs/'compile.log'],expected[out/'FreeMainWindowRankedMain.olean']):
    raise RuntimeError('receipt hashes disagree')
if (obs/'compile.log').read_text().strip()!="'FreeMainWindowRankedMain.main_at_rank' depends on axioms: [propext, Classical.choice, Quot.sound]":
    raise RuntimeError('unexpected compiler output')
for raw,item in r['guards_after'].items():
    p=Path(raw)
    if item is None:
        if p.exists() or p.is_symlink(): raise RuntimeError('earlier shadow now exists '+raw)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch '+raw)
providers=[
 ('/tmp/p64-qcube72-actual-rank-window-generic-check02/FreeMainActualRankWindowGeneric.olean',
  root/'research/p64-qcube72-actual-rank-window-split-attempt02/observations/generic02/result.json',
  '5123144cd7ef05773b3ba5fc3e6892cea7702b126ab3e2b7afd23cef437512cb'),
 ('/tmp/p64-qcube72-rank-half-priority-check02/FreeMainRankHalf.olean',
  root/'research/p64-qcube72-rank-half-draft/observations/attempt02/result.json',
  '419eed176429e0e1f2d31f05db1963bb3d893a6d63b0f249aa89e83b6d867079'),
 ('/tmp/p64-qcube72-ranked-main-priority-check03/FreeMainRankedMain.olean',
  root/'research/p64-qcube72-ranked-main-draft/observations/attempt03/result.json',
  'be2865b509d0f2f854430a3ce10dd2f6e6474b0e9801988661349236a60c40e8')]
for obj,receipt,h in providers:
    p=json.loads(receipt.read_text())
    if (p['status'],p['exit'],p['guards_stable'],p['object_sha256'])!=('PASS',0,True,h): raise RuntimeError('provider receipt mismatch '+str(receipt))
    if r['guards_after'][obj]['sha256']!=h or str(Path(obj).parent) not in r['lean_path'].split(':'):
        raise RuntimeError('direct provider not guarded or routed '+obj)
s=(packet/'FreeMainWindowRankedMain.lean').read_text()
for line in ('(hq : 33≤qval p v)','(hMC : (p 2:V)<(p 0:V))', '(hMF : (p 3:V)<2*(p 0:V))',
             'FreeMainActualRankWindowGeneric.actual_window p v hv hz hMC hMF',
             'FreeMainRankHalf.rank_half Q XX YY RR CC GG',
             'FreeMainRankedMain.main_at_rank p v hv hz hq hw.1 hhalf'):
    if line not in s: raise RuntimeError('theorem scope changed '+line)
print(json.dumps({'status':'PASS','lean_replayed':False,'guards_checked':len(r['guards_after']),
 'direct_producers_checked':3,'scope':'q bound and two mask premises; inherited provider ancestry'},sort_keys=True))
