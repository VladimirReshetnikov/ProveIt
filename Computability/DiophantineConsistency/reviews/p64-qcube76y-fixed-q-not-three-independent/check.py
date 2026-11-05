#!/usr/bin/env python3
"""Read-only recheck of retained terminal and direct provider records."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
 raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2]; p=r/'research/p64-qcube76y-fixed-q-not-three-draft'; o=Path('/tmp/p64-qcube76y-fixed-q-not-three-priority-check02')
def digest(x): return hashlib.sha256(x.read_bytes()).hexdigest()
expected={p/'FreeMain76FixedQNotThree.lean':'2366738263d44e4f47151cdd0bddcdc6df5248f03f21f90b225d03494e647e0a',p/'check02.py':'37cafa316bf6435e0a2b68d9835f3c26c3cc3c264a65ee10e839c2a753bd0728',p/'observations/attempt02/compile.log':'5e0c88edfc7200e96c356a63359189dcbe887b449f2d7ce8dded6e6fae56de50',p/'observations/attempt02/result.json':'ce9ebcac40c25f2b00141720997462aac6c2821f8ec930253b4875f77eaf1d3b',o/'FreeMain76FixedQNotThree.olean':'4c96d138cf57ad19a37add34eacbc2a4f2f6d156baad90e235a530b07d3b7ef6',Path('/tmp/p64-qcube72-free-forward-priority-check01/P64QCube72FreeForward.olean'):'badddf6e4c51093226b934f98d67236a6a28857e4679ccc90ca29978d9e333ea',Path('/tmp/p64-qcube72-divisible-q-no-old-gamma-priority-check02/FreeMainDivisibleQNoOldGamma.olean'):'80d54d2773c0baf82ccadaffef7b2dc70ce551a28d91f6ca53f7ea81d949a528'}
for f,h in expected.items():
 if not f.is_file() or digest(f)!=h: raise ValueError(('hash',str(f)))
a=json.loads((p/'observations/attempt02/result.json').read_bytes())
if (a['status']!='PASS' or a['exit']!=0 or a['stop_reason'] is not None or not a['guards_stable'] or a['guards_before']!=a['guards_after'] or a['group_rss_samples']<1): raise ValueError('terminal state')
if (p/'observations/attempt02/result.json').read_bytes()!=(o/'result.json').read_bytes() or (p/'observations/attempt02/compile.log').read_bytes()!=(o/'compile.log').read_bytes(): raise ValueError('retained output mismatch')
for f,v in a['guards_after'].items():
 x=Path(f)
 if v is None:
  if os.path.lexists(x): raise ValueError(('unexpected guard',f))
 elif not x.is_file() or str(x.resolve())!=v['realpath'] or digest(x)!=v['sha256']: raise ValueError(('guard mismatch',f))
log=(p/'observations/attempt02/compile.log').read_text()
if log.strip()!="'FreeMain76FixedQNotThree.fixed_q_not_divisible' depends on axioms: [propext, Classical.choice, Quot.sound]": raise ValueError('axiom log')
print(json.dumps({'status':'PASS_ARTIFACT_AUDIT','guards_checked':len(a['guards_after']),'direct_providers':2,'recorded_lean_exit':a['exit'],'log_sha256':a['log_sha256'],'object_sha256':a['object_sha256'],'scope':'point-in-time direct recorded artifacts only; no Lean replay or transitive ancestry audit'},sort_keys=True,indent=2))
