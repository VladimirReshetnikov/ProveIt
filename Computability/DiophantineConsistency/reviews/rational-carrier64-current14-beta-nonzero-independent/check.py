#!/usr/bin/env python3
"""Verify retained Lean result and direct guards; does not run Lean."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2];p=r/'research/rational-carrier64-current14-actual-port-split';o=Path('/tmp/rational-carrier64-current14-beta-priority-check01')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pins={p/'Current14BetaNonzero.lean':'5bafdd5655d635580b6be367e71d7b9314ea35109a4736f6076932395d1852fb',p/'check_beta01.py':'ff58b976f9fd2db16a53d6792d69438061ded8634af049e12199fb43d927ae0e',p/'observations/beta01/result.json':'3e72bfa5ba7d4ba6fe0731404d4fa7e7662777e0dd04974521df299bc206f70a',p/'observations/beta01/compile.log':'8209e0ae0677e6ad3b3fcafa5181697a0e787e2cb1625cda0afd816a52739390',o/'Current14BetaNonzero.olean':'3cd491a204ca63a508e5f810010a71aa934f82c6c77d9f337d0f5ca43bd06a01'}
for f,h in pins.items():
 if not f.is_file() or sha(f)!=h:raise ValueError(('pin',str(f)))
providers={'/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/CurrentKernelData2011.olean':'95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896','/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Mathlib/Tactic/NormNum.olean':'54e0a5e892e05629d6b26fe7b0fcc4277a7b0f47e15d237013292829b78aee0d'}
for path,h in providers.items():
 if sha(Path(path))!=h:raise ValueError(('provider pin',path))
manifest=Path('/tmp/current14-standard-fresh-source-20261104/manifest.json'); state=Path('/tmp/current14-standard-fresh-build-20261104/state.json')
if sha(manifest)!='1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749' or sha(state)!='f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014':raise ValueError('base pins')
m=json.loads(manifest.read_bytes()); b=json.loads(state.read_bytes())
if b['status']!='PASS' or b['source_status']!='CURRENT_AT_FINAL_CHECK' or b['manifest_sha256']!=sha(manifest):raise ValueError('base status')
for short in ('CurrentKernelData2011','CurrentMaskData2011'):
 name='DiophantineConsistency.'+short; row=next(x for x in b['records'] if x['module']==name); src=Path('/tmp/current14-standard-fresh-source-20261104/src/DiophantineConsistency')/(short+'.lean'); work=r/'Lean/DiophantineConsistency'/(short+'.lean'); obj=Path('/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency')/(short+'.olean')
 if row['exit']!=0 or sha(src)!=row['source_sha256'] or sha(work)!=row['source_sha256'] or m['sources'][name]['sha256']!=row['source_sha256'] or sha(obj)!=row['object_sha256'] or sha(Path(row['log']))!=row['log_sha256']:raise ValueError(('base producer',short))
 if set(row['direct_inputs'])-{'Init'}!=set(m['sources'][name]['imports']):raise ValueError(('base direct names',short))
 for entry in row['direct_inputs'].values():
  if sha(Path(entry['path']))!=entry['sha256']:raise ValueError(('base direct input',short))
a=json.loads((p/'observations/beta01/result.json').read_bytes())
if a['status']!='PASS' or a['exit']!=0 or a['stop_reason'] is not None or not a['guards_stable'] or a['guards_before']!=a['guards_after'] or a['group_rss_samples']<1:raise ValueError('terminal')
if (p/'observations/beta01/result.json').read_bytes()!=(o/'result.json').read_bytes() or (p/'observations/beta01/compile.log').read_bytes()!=(o/'compile.log').read_bytes():raise ValueError('retained files')
for f,v in a['guards_after'].items():
 x=Path(f)
 if v is None:
  if os.path.lexists(x):raise ValueError(('shadow',f))
 elif not x.is_file() or str(x.resolve())!=v['realpath'] or sha(x)!=v['sha256']:raise ValueError(('guard',f))
log=(o/'compile.log').read_text().strip()
if log!="'DiophantineConsistency.Current14BetaNonzero.actual_beta_ne' depends on axioms: [propext, Classical.choice, Quot.sound]":raise ValueError('axiom report')
print(json.dumps({'status':'PASS_ARTIFACT_RECHECK','guards_checked':len(a['guards_after']),'recorded_lean_exit':a['exit'],'direct_providers':'CurrentKernelData2011 and Mathlib NormNum','object_sha256':a['object_sha256'],'scope':'Point-in-time direct captured guards, no Lean replay or transitive audit.'},sort_keys=True,indent=2))
