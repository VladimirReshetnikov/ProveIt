#!/usr/bin/env python3
"""Verify retained Lean result and direct guards; does not run Lean."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2];p=r/'research/p64-qcube72-scale-rigidity-draft';o=Path('/tmp/p64-qcube72-scale-rigidity-priority-check01')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pins={p/'FreeMainScaleRigidity.lean':'bfac36175e2e1b2374070520bc093e0d993ccf562a967d5616c3a80c7d0a5050',p/'check01.py':'72be6c4f1ef609156bbd87f1f5abfb5c6e938dffc3aadc81d1ffa96c31ede80c',p/'observations/attempt01/result.json':'66c0b65df5b1232da05f2ed7e08d15259878fd66537e634f7d6334ad7ee770cb',p/'observations/attempt01/compile.log':'1a878e175fbcb99b9b16eb0b56e87d93d995eb9c96a4595e533d44ff1dfa434b',o/'FreeMainScaleRigidity.olean':'e941510c2b0d68559d80a4264c11ac3cf0c2714c00dd3335f9e754e9a2cf5fcc',Path('/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/ArithmeticPellCongruences.olean'):'ff395c82ca9ea770a64ec69e4b4b7f8e1e2d655d67db4831af39a2d8a78ae664'}
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
if log!="'FreeMainScaleRigidity.same_rank_root_carrier' depends on axioms: [propext, Classical.choice, Quot.sound]":raise ValueError('axiom report')
print(json.dumps({'status':'PASS_ARTIFACT_RECHECK','guards_checked':len(a['guards_after']),'recorded_lean_exit':a['exit'],'direct_provider':'ArithmeticPellCongruences','object_sha256':a['object_sha256'],'scope':'Point-in-time direct captured guards, no Lean replay or transitive audit.'},sort_keys=True,indent=2))
