#!/usr/bin/env python3
"""Verify retained Lean result and direct guards; does not run Lean."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2];p=r/'research/p64-qcube72-actual-first-ordinate-unique-draft';o=Path('/tmp/p64-qcube72-actual-first-ordinate-unique-priority-check01')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pins={p/'FreeMainActualFirstOrdinateUnique.lean':'9b2e4519f7417e01905b286be8853781d9060d580e010ffc35653c206ab93c3d',p/'check01.py':'ea85ebd06152d1404d6550a5a7b0736237358c7e9a5577ba66c2e840969abd3a',p/'observations/attempt01/result.json':'0ea8d22fdecd9cbe19f7b5ee1fad89292efa88273f4be860b97bb0541bb6220e',p/'observations/attempt01/compile.log':'d93b5e5f876951f2e1ed006ef52d363308dbb1ca80df0a966cdbef670b9b7444',o/'FreeMainActualFirstOrdinateUnique.olean':'c37a0740ec76365e3e1aa2d848dad873ff3a3a434f7a25f1fa0a974ecc4f88bc'}
for f,h in pins.items():
 if not f.is_file() or sha(f)!=h:raise ValueError(('pin',str(f)))
providers={'/tmp/p64-qcube72-first-ordinate-unique-priority-check02/FreeMainFirstOrdinateUnique.olean':'04dda4bb8fa0ee5b7d1b118a0bafc3364b68767809e3bcaa5828f819a50e23e3','/tmp/p64-qcube72-first-index-extraction-priority-check01/FreeMainFirstIndexExtraction.olean':'67ed132545d507e96b24bf023cf91a51c6b5623902889bc36daaa55ad39ad785','/tmp/p64-qcube72-conditional-rank-priority-check01/FreeMainConditionalRank.olean':'5aaee0759cb98c0e1cafcc2c3a3d42c016b9f65c9827d8e584c46192c0226d34'}
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
if log!="'FreeMainActualFirstOrdinateUnique.same_k' depends on axioms: [propext, Classical.choice, Quot.sound]":raise ValueError('axiom report')
print(json.dumps({'status':'PASS_ARTIFACT_RECHECK','guards_checked':len(a['guards_after']),'recorded_lean_exit':a['exit'],'direct_providers':'three pinned imports rechecked via captured guards','object_sha256':a['object_sha256'],'scope':'Point-in-time direct captured guards, no Lean replay or transitive audit.'},sort_keys=True,indent=2))
