#!/usr/bin/env python3
"""Verify retained Lean result and direct guards; does not run Lean."""
import hashlib,json,os,sys,re
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2];p=r/'research/rational-carrier64-current14-specialization';o=Path('/tmp/rational-carrier64-current14-specialization-priority-check01')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pins={p/'RationalCarrier64CurrentSpecialization.lean':'54e296167342fbca0f121b985921338d90ae8580e2ce85d30127687768ce279e',p/'check01.py':'970ea6463721b6ff432e538fe31d5d9775ccba64594cd9edb99eb1651559a1b1',p/'observations/attempt01/result.json':'c2145d74a7879cc6644662fe2bb26fe22759570ae92a59ed6dfa037472da661f',p/'observations/attempt01/compile.log':'adfa741ec6bd582554950952cf3b1c34f46fcb39e5f3b60796f162dac8fd8687',o/'RationalCarrier64CurrentSpecialization.olean':'d46386e6cec9201c5589eca2328da49144696c32252325160d7329e1b44d2d6e'}
for f,h in pins.items():
 if not f.is_file() or sha(f)!=h:raise ValueError(('pin',str(f)))
providers={'/tmp/rational-carrier64-current14-base-priority-check04/RationalCarrier64Current.olean':'ac3ccf83d8c6c49be8f7b9d306311f2d6fe42f317a4d7fc9b5f875890526b34b','/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Mathlib/Data/Rat/Cast/Lemmas.olean':'c1e2ff937444031d0fcb29196353fb43c62c75960ed0e1e00788af13cf8ec579'}
for path,h in providers.items():
 if sha(Path(path))!=h:raise ValueError(('provider pin',path))
prior=Path('/tmp/rational-carrier64-current14-base-priority-check04/result.json'); base=Path('/tmp/current14-standard-fresh-build-20261104/state.json'); manifest=Path('/tmp/current14-standard-fresh-source-20261104/manifest.json')
if sha(prior)!='1aa7f92b832669e21aebae740f5df7ffad372d0ccd76ca7a196d2f58ae0d1ca0' or sha(base)!='f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014' or sha(manifest)!='1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749':raise ValueError('inherited current14 provenance pins')
pr=json.loads(prior.read_bytes()); bs=json.loads(base.read_bytes()); mod='DiophantineConsistency.CurrentEquationSyntax2011'; br=next(x for x in bs['records'] if x['module']==mod)
if bs['manifest_sha256']!=sha(manifest) or not pr['guards_stable']:raise ValueError('base manifest/guard link')
if pr['status']!='PASS' or pr['exit']!=0 or pr['object_sha256']!=providers['/tmp/rational-carrier64-current14-base-priority-check04/RationalCarrier64Current.olean'] or bs['status']!='PASS' or bs['source_status']!='CURRENT_AT_FINAL_CHECK' or br['exit']!=0 or br['object_sha256']!='28e2a026978eb60c2fb0ef494b1c7256a1b1aa354ac4ee9f3688a9433d48daae':raise ValueError('inherited base record')
syntax=Path('/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/CurrentEquationSyntax2011.olean')
if sha(syntax)!=br['object_sha256']:raise ValueError('inherited syntax object drift')
a=json.loads((p/'observations/attempt01/result.json').read_bytes())
if a['lean_path'].split(':')!=['/tmp/rational-carrier64-current14-base-priority-check04','/tmp/current14-standard-fresh-build-20261104/lib','/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib']:raise ValueError('unexpected provider search path')
if a['status']!='PASS' or a['exit']!=0 or a['stop_reason'] is not None or not a['guards_stable'] or a['guards_before']!=a['guards_after'] or a['group_rss_samples']<1:raise ValueError('terminal')
if (p/'observations/attempt01/result.json').read_bytes()!=(o/'result.json').read_bytes() or (p/'observations/attempt01/compile.log').read_bytes()!=(o/'compile.log').read_bytes():raise ValueError('retained files')
for f,v in a['guards_after'].items():
 x=Path(f)
 if v is None:
  if os.path.lexists(x):raise ValueError(('shadow',f))
 elif not x.is_file() or str(x.resolve())!=v['realpath'] or sha(x)!=v['sha256']:raise ValueError(('guard',f))
log=(o/'compile.log').read_text().strip()
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",log)
expected=['DiophantineConsistency.RationalCarrier64CurrentSpecialization.'+x for x in ('value65_map','rational_value_eq','rational_zero_iff','positive_zero_iff')]
if [name for name,_ in reports]!=expected or any(' '.join(body.split())!='propext, Classical.choice, Quot.sound' for _,body in reports):raise ValueError('axiom reports')
print(json.dumps({'status':'PASS_ARTIFACT_RECHECK','guards_checked':len(a['guards_after']),'recorded_lean_exit':a['exit'],'direct_providers':'RationalCarrier64Current and Mathlib Rat cast lemmas','object_sha256':a['object_sha256'],'scope':'Point-in-time direct captured guards, no Lean replay or transitive audit.'},sort_keys=True,indent=2))
