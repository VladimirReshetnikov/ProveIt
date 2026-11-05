#!/usr/bin/env python3
"""Check the fixed compact ranked-main artifacts without invoking Lean."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-fixed-compact-ranked-main-draft'
obs=packet/'observations/attempt01'
tmp=Path('/tmp/p64-qcube72-fixed-compact-ranked-main-check01')
pins={'source.lean':'79eedcd56d95f2cc761609536bcf19c28119d2889806d0d3b480d573fa938159',
      'check.py':'b7e5656884b8dcddcaa1077d357f64b7c37356778a7bff7d06f81927caf99c46',
      'compile.log':'b74bb2fb4437b0c1276782d2398978878acf30ad982f7cc295c3cbf95528247b',
      'result.json':'51251652e0ce6a4ff041f8d249a6439e2d032cd379df9dbfe20b60758166a76a',
      'object.olean.bin':'eb8fbc81679bd6193c8879510c34e1263f8baef31a079abb0c3226ce449f4079'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in pins.items():
    if not (obs/n).is_file() or sha(obs/n)!=h: raise RuntimeError('snapshot mismatch '+n)
for cur,saved in [(packet/'FreeMainFixedCompactRankedMain.lean',obs/'source.lean'),
                  (packet/'check.py',obs/'check.py'),
                  (tmp/'FreeMainFixedCompactRankedMain.olean',obs/'object.olean.bin')]:
    if cur.read_bytes()!=saved.read_bytes(): raise RuntimeError('live/terminal mismatch '+str(cur))
r=json.loads((obs/'result.json').read_text()); o=json.loads((obs/'observation.json').read_text())
if (r['status'],r['exit'],r['failure'],r['guards_stable'])!=('PASS',0,None,True): raise RuntimeError('failed run')
if (o['observed_session_exit'],o['lean_child_exit'])!=(0,0) or o['sha256']!=pins: raise RuntimeError('terminal observation mismatch')
if r['guards_before']!=r['guards_after'] or not r['samples']: raise RuntimeError('guard/sample mismatch')
if (r['process_receipt']['exit'],r['process_receipt']['direct_child_reaped'],r['process_receipt']['session_drained'])!=(0,True,True):
    raise RuntimeError('child/session not cleanly ended')
if (r['source_sha256'],r['runner_sha256'],r['log_sha256'],r['object_sha256'])!=(pins['source.lean'],pins['check.py'],pins['compile.log'],pins['object.olean.bin']):
    raise RuntimeError('receipt hash mismatch')
if (obs/'compile.log').read_text().strip()!="'FreeMainFixedCompactRankedMain.fixed_main_at_rank' depends on axioms: [propext, Classical.choice, Quot.sound]":
    raise RuntimeError('unexpected compiler report')
for name,item in r['guards_after'].items():
    p=Path(name)
    if item is None:
        if p.exists() or p.is_symlink(): raise RuntimeError('guarded shadow present '+name)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch '+name)
providers={
 '/tmp/p64-qcube72-symbolic-port-ranked-main-priority-check03/FreeMainSymbolicPortRankedMain.olean':'f5676747b761614f746b9dc6861c329b17f146520f229b6838b729a4d2fc009f',
 '/tmp/p64-qcube72-compact-port-opaque-check02/FreeMainActualRankWindowCompact.olean':'f71306eaa4345a383e3721028a7c7e0aaf0b5d5276443792e9d2e787fbedd5b3',
 '/tmp/p64-independent-captured-replay/lib/CompactSymbolicMaskData.olean':'bce797f5b40fa75f130af592ed0c41e755f888ce9693538d1020cbd230004437'}
for path,h in providers.items():
    if r['guards_after'][path]['sha256']!=h or str(Path(path).parent) not in r['lean_path']:
        raise RuntimeError('provider mismatch '+path)
receipts=[
 ('research/p64-qcube72-symbolic-port-ranked-main-draft/observations/attempt03/result.json',list(providers.values())[0]),
 ('research/p64-qcube72-compact-port-opaque-attempt02/observations/attempt02/result.json',list(providers.values())[1])]
for rel,h in receipts:
    p=json.loads((root/rel).read_text())
    if (p['status'],p['exit'],p['object_sha256'])!=('PASS',0,h): raise RuntimeError('producer receipt mismatch '+rel)
s=(obs/'source.lean').read_text()
for x in ('private theorem compactPorts_eq', 'CompactSymbolicPorts.ports CompactFixedBeta.betaNat K',
          'CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat',
          'have hwindow := compact_window K v hv hz', 'CompactSymbolicMaskData.data (V:=V)',
          'FreeMainSymbolicPortRankedMain.main_at_rank', 'hb.2.2.2 hb.1 hb.2.1',
          'FreeMainActualRankWindowGeneric.rank p v', 'FreeMainAuxNorm.rank p v'):
    if x not in s: raise RuntimeError('source theorem changed '+x)
rank_sources=[
 (root/'research/p64-qcube72-actual-rank-window-split-attempt02/FreeMainActualRankWindowGeneric.lean',
  '98feada0e3eb4a6478bea73c980f3c31e8a7d600da7cecbecbe1105de913d68a'),
 (root/'research/p64-qcube72-natural-norms-draft/FreeMainAuxNorm.lean',
  '6e7e14a1ecfa3c42bdba994ce341f44e88a7ad64febf1768c672c4948ec4d32e')]
defs=[]
for path,h in rank_sources:
    if sha(path)!=h: raise RuntimeError('rank definition source drift '+str(path))
    text=path.read_text(); start=text.index('def rank ('); end=text.index('\n\n',start)
    defs.append(text[start:end])
if defs[0]!=defs[1]: raise RuntimeError('rank definitions differ')
bridge=root/'research/p64-qcube72-window-ranked-main-bridge-draft/FreeMainWindowRankedMain.lean'
if sha(bridge)!='3afeff3cacbb6180ae1040d2daff8dce7aad5da9394f7793e0f8cc4260195d50': raise RuntimeError('bridge source drift')
if 'change 0<R ∧ (ι R:DiffRing V)+1' not in bridge.read_text(): raise RuntimeError('rank definitional change absent')
print(json.dumps({'status':'PASS','lean_replayed':False,'guards_checked':len(r['guards_after']),
 'rank_definitions_equal':True,'scope':'fixed compact tuple, arbitrary natural K, actual-zero rank window and main coordinates; captured ancestry'},sort_keys=True))
