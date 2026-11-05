#!/usr/bin/env python3
"""Verify retained Lean result and direct guards; does not run Lean."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2];p=r/'research/p64-qcube72-two-zero-scale-obstruction-draft';o=Path('/tmp/p64-qcube72-two-zero-scale-obstruction-priority-check02')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pins={p/'FreeMainTwoZeroScaleObstruction.lean':'ed297bb51695c2cf985a945fdd299f3888ee44be603c906373ae3d5c219c24a6',p/'check02.py':'66b6f86561e448620211b75532df69d25ccb3a62c72fa4912d7b3777f04512bc',p/'observations/attempt02/result.json':'b123c72d05826febd36924fd04d98e410ed0369452a78c45611b0d2c0c751df0',p/'observations/attempt02/compile.log':'904506a9114d85b14a96d4d578eaeac81d8c5073885227f8af2371156fc28f52',o/'FreeMainTwoZeroScaleObstruction.olean':'c4d54c546d6fa15cd0a98434776e0afa2517d766025c32bd8503be37ada9999f'}
for f,h in pins.items():
 if not f.is_file() or sha(f)!=h:raise ValueError(('pin',str(f)))
a=json.loads((p/'observations/attempt02/result.json').read_bytes())
if a['status']!='PASS' or a['exit']!=0 or a['stop_reason'] is not None or not a['guards_stable'] or a['guards_before']!=a['guards_after'] or a['group_rss_samples']<1:raise ValueError('terminal')
if (p/'observations/attempt02/result.json').read_bytes()!=(o/'result.json').read_bytes() or (p/'observations/attempt02/compile.log').read_bytes()!=(o/'compile.log').read_bytes():raise ValueError('retained files')
for f,v in a['guards_after'].items():
 x=Path(f)
 if v is None:
  if os.path.lexists(x):raise ValueError(('shadow',f))
 elif not x.is_file() or str(x.resolve())!=v['realpath'] or sha(x)!=v['sha256']:raise ValueError(('guard',f))
log=(o/'compile.log').read_text().strip()
if log!="'FreeMainTwoZeroScaleObstruction.two_zero_no_old_gamma' depends on axioms: [propext, Classical.choice, Quot.sound]":raise ValueError('axiom report')
print(json.dumps({'status':'PASS_ARTIFACT_RECHECK','guards_checked':len(a['guards_after']),'recorded_lean_exit':a['exit'],'direct_providers':'both pinned imports rechecked via captured guards','object_sha256':a['object_sha256'],'scope':'Point-in-time direct captured guards, no Lean replay or transitive audit.'},sort_keys=True,indent=2))
