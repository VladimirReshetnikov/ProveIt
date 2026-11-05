#!/usr/bin/env python3
"""Verify retained Lean result and direct guards; does not run Lean."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2];p=r/'research/p64-qcube72-first-ordinate-unique-draft';o=Path('/tmp/p64-qcube72-first-ordinate-unique-priority-check02')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pins={p/'FreeMainFirstOrdinateUnique.lean':'7650676de99166ec6927d10f1ae351e0f0d4ee0ba919314cb5d74eb97241dd27',p/'check02.py':'7016cdb7ed9174895ce1ab2e033ad009c27276a01257d7992e2e6ede6e0d5de7',p/'observations/attempt02/result.json':'a3a0dfd6435a23732fe3a0fd54bb9fa901d73251a42e75534ffe1378e9f01af7',p/'observations/attempt02/compile.log':'951fcd8b74c75fc55c13fd6c292925128ceeb1c09f4050165b67659a6af65272',o/'FreeMainFirstOrdinateUnique.olean':'04dda4bb8fa0ee5b7d1b118a0bafc3364b68767809e3bcaa5828f819a50e23e3',Path('/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/ArithmeticPellPowerRecovery.olean'):'81ac9f2d4ffcf1ad8a5bce697cc6369a21a1df07aa9fdf10a8700e63755e392f'}
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
expected="\n".join("\'FreeMainFirstOrdinateUnique."+n+"\' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in ("double_lt_of_index_lt","not_double","first_index_unique"))
if log!=expected:raise ValueError('axiom report')
print(json.dumps({'status':'PASS_ARTIFACT_RECHECK','guards_checked':len(a['guards_after']),'recorded_lean_exit':a['exit'],'direct_provider':'ArithmeticPellPowerRecovery','object_sha256':a['object_sha256'],'scope':'Point-in-time direct captured guards, no Lean replay or transitive audit.'},sort_keys=True,indent=2))
