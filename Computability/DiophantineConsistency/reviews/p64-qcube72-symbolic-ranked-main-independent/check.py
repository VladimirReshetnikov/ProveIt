#!/usr/bin/env python3
"""Audit the symbolic-port ranked-main terminal result without Lean replay."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-symbolic-port-ranked-main-draft'
obs=packet/'observations/attempt03'
out=Path('/tmp/p64-qcube72-symbolic-port-ranked-main-priority-check03')
pins={packet/'FreeMainSymbolicPortRankedMain.lean':'24b2bee0a06395d800ffd99746ddc511ea08a6545c3574986d8d415abd73709d',
 packet/'check03.py':'a114656bbaea7aed2603ce8ab30dd1fd751b57974b8b90a162b19adf436c232c',
 packet/'missing_child.py':'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
 obs/'compile.log':'2b4f96a55761c3ba1e0b6a6a6aac1a024da660afbf5d9327b53ab65eaf018d52',
 obs/'result.json':'2a912a0311acb1c7568d315573f588db5aa9597a0d2e073137ca93fac9fd2ce1',
 out/'FreeMainSymbolicPortRankedMain.olean':'f5676747b761614f746b9dc6861c329b17f146520f229b6838b729a4d2fc009f'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in pins.items():
    if not p.is_file() or p.is_symlink() or sha(p)!=h: raise RuntimeError('artifact mismatch '+str(p))
for name in ('compile.log','result.json'):
    if (out/name).read_bytes()!=(obs/name).read_bytes(): raise RuntimeError('terminal copy mismatch '+name)
r=json.loads((obs/'result.json').read_text())
if (r['status'],r['exit'],r['stop_reason'],r['guards_stable'])!=('PASS',0,None,True): raise RuntimeError('bad terminal receipt')
if r['guards_before']!=r['guards_after'] or not r['group_rss_samples']: raise RuntimeError('guard/sample failure')
if (r['runner_sha256'],r['missing_child_helper_sha256'],r['log_sha256'],r['object_sha256']) != (
 pins[packet/'check03.py'],pins[packet/'missing_child.py'],pins[obs/'compile.log'],pins[out/'FreeMainSymbolicPortRankedMain.olean']):
    raise RuntimeError('receipt hashes disagree')
names=('q_lower','main_at_rank')
want='\n'.join(f"'FreeMainSymbolicPortRankedMain.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names)
if (obs/'compile.log').read_text().strip()!=want: raise RuntimeError('unexpected compiler output')
for raw,item in r['guards_after'].items():
    p=Path(raw)
    if item is None:
        if p.exists() or p.is_symlink(): raise RuntimeError('shadow exists '+raw)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch '+raw)
providers={
 '/tmp/p64-qcube72-window-ranked-main-priority-check02/FreeMainWindowRankedMain.olean':'3597c62070070a2cc761b9c5a182de486f7ae04a71f139aadc45cad09513db15',
 '/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/CompactSymbolicPorts.olean':'69927a2a645ea7c4ba99f7413357bfbbd7a344b2e0a026f08392e67870c8bff5',
 '/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/ArithmeticStandardCasts.olean':'c992bafb003c67229c756a634d31c11ecfb942839904367554488ba27ddc597a'}
for path,h in providers.items():
    if r['guards_after'][path]['sha256']!=h: raise RuntimeError('provider mismatch '+path)
base=json.loads((root/'research/p64-qcube72-window-ranked-main-bridge-draft/observations/attempt02/result.json').read_text())
if (base['status'],base['exit'],base['object_sha256'])!=('PASS',0,providers[next(iter(providers))]): raise RuntimeError('bridge producer mismatch')
s=(packet/'FreeMainSymbolicPortRankedMain.lean').read_text()
for x in ('(hb : b+1=Exp.exp (590069:V)) (hJ : 0<J)', 'Exp.exp (6:V)=(64:V)',
          'exp_monotone_le.mpr', '(hbeta : (beta:V)+1=Exp.exp (590069:V))',
          '(hL : (L:V)<(beta:V))', '(hH : (beta:V)+(H:V)<2*(beta:V))',
          'FreeMainWindowRankedMain.main_at_rank p v hv hz hq hMC hMF'):
    if x not in s: raise RuntimeError('theorem scope changed '+x)
print(json.dumps({'status':'PASS','lean_replayed':False,'guards_checked':len(r['guards_after']),
                  'scope':'variable ports under explicit exponential and two mask bounds; inherited captured ancestry'},sort_keys=True))
