#!/usr/bin/env python3
"""Verify retained Lean result and direct guards; does not run Lean."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2];p=r/'research/p64-qcube72-to-76-fixed-scale-obstruction-draft';o=Path('/tmp/p64-qcube72-to-76-fixed-scale-obstruction-priority-check01')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pins={p/'FreeMain72To76FixedScaleObstruction.lean':'5ddc1fbd656e2ad92c32c3db8c8bc474dba563854f43fb94cf80a5b873e5263c',p/'check01.py':'74336a37f4dda2acaad3d38280327649bd6d4d8c749989a1aff1abc0b41d6d35',p/'observations/attempt01/result.json':'9468a7a98cbb2c755f3209303bc793fae65f3fc15ad4377762065ea5864edeaa',p/'observations/attempt01/compile.log':'0d9017aacb657fed9f10467132691b26fe65b41925c6ed99928eb6f133c25349',o/'FreeMain72To76FixedScaleObstruction.olean':'a64cc4b23331213e9d8d9440e8ffd0ca7254199cfa7c9842c0c4141347f49b43'}
for f,h in pins.items():
 if not f.is_file() or sha(f)!=h:raise ValueError(('pin',str(f)))
a=json.loads((p/'observations/attempt01/result.json').read_bytes())
if a['status']!='PASS' or a['exit']!=0 or a['stop_reason'] is not None or not a['guards_stable'] or a['guards_before']!=a['guards_after'] or a['group_rss_samples']<1:raise ValueError('terminal')
if (p/'observations/attempt01/result.json').read_bytes()!=(o/'result.json').read_bytes() or (p/'observations/attempt01/compile.log').read_bytes()!=(o/'compile.log').read_bytes():raise ValueError('retained files')
for f,v in a['guards_after'].items():
 x=Path(f)
 if v is None:
  if os.path.lexists(x):raise ValueError(('shadow',f))
 elif not x.is_file() or str(x.resolve())!=v['realpath'] or sha(x)!=v['sha256']:raise ValueError(('guard',f))
log=(o/'compile.log').read_text().strip()
if log!="'FreeMain72To76FixedScaleObstruction.no_fixed_scale_target' depends on axioms: [propext, Classical.choice, Quot.sound]":raise ValueError('axiom report')
print(json.dumps({'status':'PASS_ARTIFACT_RECHECK','guards_checked':len(a['guards_after']),'recorded_lean_exit':a['exit'],'direct_providers':'both pinned imports rechecked via captured guards','object_sha256':a['object_sha256'],'scope':'Point-in-time direct captured guards, no Lean replay or transitive audit.'},sort_keys=True,indent=2))
