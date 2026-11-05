#!/usr/bin/env python3
"""Verify retained Lean result and direct guards; does not run Lean."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2];p=r/'research/p64-qcube72-to-76-three-scale-obstruction-draft';o=Path('/tmp/p64-qcube72-to-76-three-scale-obstruction-priority-check01')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pins={p/'FreeMain72To76ThreeScaleObstruction.lean':'47d94b987688def621bd44a3cfa6b93901caba7db3bccfb8d784acb7c971f6fa',p/'check01.py':'e3567a92398f98664c61e193aacff69f70d27d8214114aeb89a4a6879a506347',p/'observations/attempt01/result.json':'03a3f965de715b6058b95b1913e74fbf76e9bb045d9db753c083a557c4f6d643',p/'observations/attempt01/compile.log':'b9107a0a1791c0b1b5ac384c5a37282259a1a53a23f8376348cc2ee16a437aa8',o/'FreeMain72To76ThreeScaleObstruction.olean':'c989d12b1a41a9965e0b392a0b625dd9f46724683ca0214bf7083e11044b9de3'}
for f,h in pins.items():
 if not f.is_file() or sha(f)!=h:raise ValueError(('pin',str(f)))
providers={'/tmp/p64-qcube72-free-forward-priority-check01/P64QCube72FreeForward.olean':'badddf6e4c51093226b934f98d67236a6a28857e4679ccc90ca29978d9e333ea','/tmp/p64-qcube72-two-zero-scale-obstruction-priority-check02/FreeMainTwoZeroScaleObstruction.olean':'c4d54c546d6fa15cd0a98434776e0afa2517d766025c32bd8503be37ada9999f','/tmp/p64-qcube72-actual-first-ordinate-unique-priority-check01/FreeMainActualFirstOrdinateUnique.olean':'c37a0740ec76365e3e1aa2d848dad873ff3a3a434f7a25f1fa0a974ecc4f88bc'}
for path,h in providers.items():
 if sha(Path(path))!=h:raise ValueError(('provider pin',path))
a=json.loads((p/'observations/attempt01/result.json').read_bytes())
if a['status']!='PASS' or a['exit']!=0 or a['stop_reason'] is not None or not a['guards_stable'] or a['guards_before']!=a['guards_after'] or a['group_rss_samples']<1:raise ValueError('terminal')
if (p/'observations/attempt01/result.json').read_bytes()!=(o/'result.json').read_bytes() or (p/'observations/attempt01/compile.log').read_bytes()!=(o/'compile.log').read_bytes():raise ValueError('retained files')
for f,v in a['guards_after'].items():
 x=Path(f)
 if v is None:
  if os.path.lexists(x):raise ValueError(('shadow',f))
 elif not x.is_file() or str(x.resolve())!=v['realpath'] or sha(x)!=v['sha256']:raise ValueError(('guard',f))
log=(o/'compile.log').read_text().strip()
if log!="'FreeMain72To76ThreeScaleObstruction.no_fixed_scale_target' depends on axioms: [propext, Classical.choice, Quot.sound]":raise ValueError('axiom report')
print(json.dumps({'status':'PASS_ARTIFACT_RECHECK','guards_checked':len(a['guards_after']),'recorded_lean_exit':a['exit'],'direct_providers':'three pinned imports rechecked via captured guards','object_sha256':a['object_sha256'],'scope':'Point-in-time direct captured guards, no Lean replay or transitive audit.'},sort_keys=True,indent=2))
