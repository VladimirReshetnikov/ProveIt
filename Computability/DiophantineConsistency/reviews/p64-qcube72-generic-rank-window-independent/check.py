#!/usr/bin/env python3
"""Inspect generic rank-window terminal artifacts without rebuilding Lean."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')

root = Path(__file__).resolve().parents[2]
packet = root/'research/p64-qcube72-actual-rank-window-split-attempt02'
obs = packet/'observations/generic02'
tmp = Path('/tmp/p64-qcube72-actual-rank-window-generic-check02')
files = {
    'source.lean':'98feada0e3eb4a6478bea73c980f3c31e8a7d600da7cecbecbe1105de913d68a',
    'check.py':'f30d53f2b0b42654961c9bab0d197013f59c7d8e42004e71731cb0f4930a3714',
    'compile.log':'7586cfe9be214ad31d1aa50039ac6232de5c2448045a3db20756f8194040d01f',
    'result.json':'1067b6d072ce4761d751f1b9c740beb0836f447cd0ddf87d9f39289a45108d94',
    'object.olean.bin':'5123144cd7ef05773b3ba5fc3e6892cea7702b126ab3e2b7afd23cef437512cb',
}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for name,h in files.items():
    if not (obs/name).is_file() or sha(obs/name)!=h: raise RuntimeError('artifact mismatch '+name)
for current, saved in [(packet/'FreeMainActualRankWindowGeneric.lean',obs/'source.lean'),
                       (packet/'check-generic.py',obs/'check.py'),
                       (tmp/'FreeMainActualRankWindowGeneric.olean',obs/'object.olean.bin')]:
    if current.read_bytes()!=saved.read_bytes(): raise RuntimeError('current or terminal copy mismatch: '+str(current))
r=json.loads((obs/'result.json').read_text()); o=json.loads((obs/'observation.json').read_text())
if (r['status'],r['exit'],r['failure'],r['guards_stable']) != ('PASS',0,None,True): raise RuntimeError('run failed')
if (o['observed_session_exit'],o['lean_child_exit']) != (0,0) or o['sha256']!=files: raise RuntimeError('observation mismatch')
if r['process_receipt']['exit']!=0 or not r['process_receipt']['direct_child_reaped'] or not r['process_receipt']['session_drained']:
    raise RuntimeError('child process did not exit cleanly')
if r['guards_before']!=r['guards_after'] or not r['samples']: raise RuntimeError('guard/sample mismatch')
if (r['source_sha256'],r['runner_sha256'],r['log_sha256'],r['object_sha256']) != (files['source.lean'],files['check.py'],files['compile.log'],files['object.olean.bin']):
    raise RuntimeError('receipt hash mismatch')
if (obs/'compile.log').read_text().strip() != "'FreeMainActualRankWindowGeneric.actual_window' depends on axioms: [propext, Classical.choice, Quot.sound]":
    raise RuntimeError('unexpected compiler output')
for raw,item in r['guards_after'].items():
    p=Path(raw)
    if item is None:
        if p.exists() or p.is_symlink(): raise RuntimeError('shadow now exists: '+raw)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch: '+raw)
residual='/tmp/p64-qcube72-residuals-priority-check01/FreeMainGraphResiduals.olean'
resid_receipt=json.loads((root/'research/p64-qcube72-residuals-draft/observations/attempt01/result.json').read_text())
if (resid_receipt['status'],resid_receipt['exit'],resid_receipt['object_sha256']) != ('PASS',0,r['guards_after'][residual]['sha256']):
    raise RuntimeError('residual provider mismatch')
window='/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/Compact44/P72Window.olean'
if r['guards_after'][window]['sha256']!='c59b720bc01ac215bcc024b41a2fd321cc5ea2e0a3c208ebda0c8af098b7882e':
    raise RuntimeError('captured window provider mismatch')
source=(obs/'source.lean').read_text()
for s in ('(hMC : (p 2:V) < (p 0:V))', '(hMF : (p 3:V) < 2*(p 0:V))',
          '0 < rank p v ∧', 'FreeMainGraphResiduals.residuals p v hv hz',
          'P72Window.window_ring hQ hF1 hA1 hC hJ1 hBJ hMC1 hMF1'):
    if s not in source: raise RuntimeError('source scope changed: '+s)
print(json.dumps({'status':'PASS','lean_replayed':False,'guard_entries_checked':len(r['guards_after']),
    'scope':'generic rank window only; captured P72Window provider; transitive/dynamic ancestry inherited'},sort_keys=True))
