#!/usr/bin/env python3
"""Audit the captured compact-port rank window without running Lean."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-compact-port-opaque-attempt02'
obs=packet/'observations/attempt02'
tmp=Path('/tmp/p64-qcube72-compact-port-opaque-check02')
pins={'source.lean':'2d9c96320d64a0f6dccc927ea4e4fc22d816cf0eabdc8799ce83947bc091a35b',
      'check.py':'45d53d57288fa7a5afc38496f9d6785c9191b308878255e4097c514635fd2228',
      'compile.log':'2d36f4caa18577d347461cf62f87b4138c2dd724bc7487b8dfa5cfc6d9a39beb',
      'result.json':'cdc984696f5568e060f7938d320de1a0330bb2948616ac5dd414ae3895cc8933',
      'object.olean.bin':'f71306eaa4345a383e3721028a7c7e0aaf0b5d5276443792e9d2e787fbedd5b3'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in pins.items():
    if not (obs/n).is_file() or sha(obs/n)!=h: raise RuntimeError('snapshot mismatch '+n)
for current,saved in [(packet/'FreeMainActualRankWindowCompact.lean',obs/'source.lean'),
                      (packet/'check.py',obs/'check.py'),
                      (tmp/'FreeMainActualRankWindowCompact.olean',obs/'object.olean.bin')]:
    if current.read_bytes()!=saved.read_bytes(): raise RuntimeError('current/terminal copy mismatch '+str(current))
r=json.loads((obs/'result.json').read_text()); o=json.loads((obs/'observation.json').read_text())
if (r['status'],r['exit'],r['failure'],r['guards_stable'])!=('PASS',0,None,True): raise RuntimeError('failed receipt')
if (o['observed_session_exit'],o['lean_child_exit'])!=(0,0) or o['sha256']!=pins: raise RuntimeError('observed terminal mismatch')
if r['guards_before']!=r['guards_after'] or not r['samples']: raise RuntimeError('unstable guards or missing samples')
if not r['process_receipt']['direct_child_reaped'] or not r['process_receipt']['session_drained'] or r['process_receipt']['exit']!=0:
    raise RuntimeError('child/session not cleanly ended')
if (r['source_sha256'],r['runner_sha256'],r['log_sha256'],r['object_sha256'])!=(pins['source.lean'],pins['check.py'],pins['compile.log'],pins['object.olean.bin']):
    raise RuntimeError('receipt hashes disagree')
if (obs/'compile.log').read_text().strip()!="'FreeMainActualRankWindowCompact.compact_window' depends on axioms: [propext, Classical.choice, Quot.sound]":
    raise RuntimeError('unexpected compiler log')
for name,item in r['guards_after'].items():
    p=Path(name)
    if item is None:
        if p.exists() or p.is_symlink(): raise RuntimeError('shadow exists '+name)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard changed '+name)
providers={
 '/tmp/p64-qcube72-actual-rank-window-generic-check02/FreeMainActualRankWindowGeneric.olean':'5123144cd7ef05773b3ba5fc3e6892cea7702b126ab3e2b7afd23cef437512cb',
 '/tmp/p64-independent-captured-replay/lib/CompactSymbolicMaskData.olean':'bce797f5b40fa75f130af592ed0c41e755f888ce9693538d1020cbd230004437',
 '/tmp/p64-independent-captured-replay/lib/CompactGenericPortProjections.olean':'d658eaf6f7d7bcbe6b499ef3584c261af6a3a42e97e7678112e205a8e22d24f7'}
for path,h in providers.items():
    if r['guards_after'][path]['sha256']!=h or str(Path(path).parent) not in r['lean_path']:
        raise RuntimeError('provider hash or path mismatch '+path)
base=json.loads((root/'research/p64-qcube72-actual-rank-window-split-attempt02/observations/generic02/result.json').read_text())
if (base['status'],base['exit'],base['object_sha256'])!=('PASS',0,providers[next(iter(providers))]):
    raise RuntimeError('generic theorem producer mismatch')
s=(obs/'source.lean').read_text()
for x in ('CompactSymbolicPorts.ports CompactFixedBeta.betaNat K',
          'CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat',
          'CompactGenericPortProjections.at_zero', 'CompactGenericPortProjections.at_two',
          'CompactGenericPortProjections.at_three', 'attribute [local irreducible] compactPorts',
          'CompactSymbolicMaskData.data (V:=V)', 'exact actual_window p v hv hz hMC hMF'):
    if x not in s: raise RuntimeError('compact theorem changed '+x)
print(json.dumps({'status':'PASS','lean_replayed':False,'direct_guards_checked':len(r['guards_after']),
                  'scope':'compact rank positivity/window; two captured static port providers and inherited ancestry'},sort_keys=True))
