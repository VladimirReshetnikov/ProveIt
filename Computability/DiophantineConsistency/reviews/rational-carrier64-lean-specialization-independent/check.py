#!/usr/bin/env python3
"""Verify retained Lean result and direct guards; does not run Lean."""
import hashlib,json,os,sys,re
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2];p=r/'research/rational-carrier64-lean-specialization';o=Path('/tmp/rational-carrier64-specialization-priority-check02')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pins={p/'RationalCarrier64Specialization.lean':'cdf5cf2d40c3f143dc12a286e8c5968602360cd2ea0e08c593168211e755071f',p/'check02.py':'bee197f34f4df1689888e77b534fc0c0f65d1d1b39dbcb5ffac3b3ed9aa42cd6',p/'observations/attempt02/result.json':'289a0493d7ccc0ef785c325153b135bb851dcbbe30d3430a93113ab3638b3acf',p/'observations/attempt02/compile.log':'a25238f8e48ca68092967d55ab3917344dd330b6c89b17922332b311eb8158bf',o/'RationalCarrier64Specialization.olean':'15f3ac6c4c29c8a71d0ebad456c58f2592c59407660b08a11a90ff1ac063fea8'}
for f,h in pins.items():
 if not f.is_file() or sha(f)!=h:raise ValueError(('pin',str(f)))
providers={'/tmp/rational-carrier64-identity-priority-check03/RationalCarrier64.olean':'a2aa0510f8dc710e455981b605c304c2a0dbfe75e343d443f33eac27aeef8b43','/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Mathlib/Data/Rat/Cast/Lemmas.olean':'c1e2ff937444031d0fcb29196353fb43c62c75960ed0e1e00788af13cf8ec579'}
for path,h in providers.items():
 if sha(Path(path))!=h:raise ValueError(('provider pin',path))
a=json.loads((p/'observations/attempt02/result.json').read_bytes())
if a['status']!='PASS' or a['exit']!=0 or a['stop_reason'] is not None or not a['guards_stable'] or a['guards_before']!=a['guards_after'] or a['group_rss_samples']<1:raise ValueError('terminal')
if (p/'observations/attempt02/result.json').read_bytes()!=(o/'result.json').read_bytes() or (p/'observations/attempt02/compile.log').read_bytes()!=(o/'compile.log').read_bytes():raise ValueError('retained files')
for f,v in a['guards_after'].items():
 x=Path(f)
 if v is None:
  if os.path.lexists(x):raise ValueError(('shadow',f))
 elif not x.is_file() or str(x.resolve())!=v['realpath'] or sha(x)!=v['sha256']:raise ValueError(('guard',f))
log=(o/'compile.log').read_text().strip()
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",log)
expected=['DiophantineConsistency.RationalCarrier64Specialization.'+x for x in ('rational_value_eq','rational_zero_iff','positive_zero_iff')]
if [name for name,_ in reports]!=expected or any(' '.join(body.split())!='propext, Classical.choice, Quot.sound' for _,body in reports):raise ValueError('axiom reports')
print(json.dumps({'status':'PASS_ARTIFACT_RECHECK','guards_checked':len(a['guards_after']),'recorded_lean_exit':a['exit'],'direct_providers':'RationalCarrier64 and Mathlib Rat cast lemmas','object_sha256':a['object_sha256'],'scope':'Point-in-time direct captured guards, no Lean replay or transitive audit.'},sort_keys=True,indent=2))
