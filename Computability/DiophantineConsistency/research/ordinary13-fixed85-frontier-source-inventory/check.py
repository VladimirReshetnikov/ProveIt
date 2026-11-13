from pathlib import Path
from collections import Counter,deque
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path.cwd(); repo=here.parents[1]
manifest=here/'research/ordinary13-fixed85-native-composition-draft/manifest.json'
assert sha256(manifest.read_bytes()).hexdigest()=='a4934426329ffedef443a7b6a95bd5fd09d5210c8c9014fb522deed82e65c05e'
a=json.loads(manifest.read_text());frontier=a['external_frontier'];assert len(frontier)==94 and len(set(frontier))==94
local_roots={'BusyBeaver':repo/'Computability/BusyBeaver/Lean','PAHF':repo/'Logic/Interpretability/PAHF/Lean','ZFCinPA':repo/'Logic/Interpretability/ZFCinPA/Lean','Foundation':repo/'lib/FormalizedFormalLogic-Foundation','Mathlib':repo/'.lake/packages/mathlib','Lean':Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean')}
fallback=Path('/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation')
rows=[];counts=Counter()
for module in sorted(frontier):
 family=module.split('.')[0];assert family in local_roots
 suffix=Path(*module.split('.')).with_suffix('.lean');expected=local_roots[family]/suffix
 other=fallback/suffix if family=='Foundation' else None
 if expected.is_file():
  status={'Mathlib':'mathlib_package_source','Lean':'lean_toolchain_source','Foundation':'configured_foundation_source'}.get(family,'other_repository_source_root')
  selected=expected
 elif other is not None and other.is_file():status='foundation_other_checkout_only';selected=other
 else:status='missing_in_checked_roots';selected=None
 counts[status]+=1
 rows.append({'module':module,'status':status,'configured_source':str(expected),'other_checkout_source':str(other) if other is not None else None,'found_source':str(selected) if selected is not None else None,'found_sha256':sha256(selected.read_bytes()).hexdigest() if selected is not None else None})
subrepo=repo/'lib/FormalizedFormalLogic-Foundation';gitlink=subprocess.check_output(['git','-C',str(repo),'ls-tree','HEAD','lib/FormalizedFormalLogic-Foundation'],text=True).split()[2]
configured_rev=subprocess.check_output(['git','-C',str(subrepo),'rev-parse','HEAD'],text=True).strip() if (subrepo/'Foundation').is_dir() else None
configured_clean=(subprocess.check_output(['git','-C',str(subrepo),'status','--porcelain=v1','--untracked-files=all'],text=True)=='') if configured_rev else None
fallback_rev=subprocess.check_output(['git','-C',str(fallback),'rev-parse','HEAD'],text=True).strip()
fallback_clean=subprocess.check_output(['git','-C',str(fallback),'status','--porcelain=v1','--untracked-files=all'],text=True)==''
mathlib=repo/'.lake/packages/mathlib';mathlib_rev=subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip()
lake=json.loads((repo/'lake-manifest.json').read_text());mathlib_manifest=next(p['rev'] for p in lake['packages'] if p['name']=='mathlib')
mods=a['local_modules'];target='ResidueSignFreePower';q=deque([('Fixed85Endpoint',['Fixed85Endpoint'])]);visited=set();route=None
while q:
 cur,path=q.popleft()
 if cur==target:route=path;break
 if cur in visited:continue
 visited.add(cur)
 for dep in mods.get(cur,{}).get('imports',[]):
  if dep in mods and dep not in visited:q.append((dep,path+[dep]))
assert route is not None
assert mods[target]['imports'].count('Mathlib.Tactic.Omega')==1
importer=here/mods[target]['path']
assert sha256(importer.read_bytes()).hexdigest()==mods[target]['sha256']
assert 'import Mathlib.Tactic.Omega\n' in importer.read_text()
missing=[x['module'] for x in rows if x['status']=='missing_in_checked_roots']
assert missing==['Mathlib.Tactic.Omega']
assert fallback_rev==gitlink and fallback_clean and mathlib_rev==mathlib_manifest
assert configured_rev is None or (configured_rev==gitlink and configured_clean)
print(json.dumps({'manifest_sha256':sha256(manifest.read_bytes()).hexdigest(),'counts':dict(sorted(counts.items())),'frontier_modules':rows,'foundation_gitlink':gitlink,'foundation_configured_checkout_revision':configured_rev,'foundation_configured_checkout_clean':configured_clean,'foundation_other_checkout_revision':fallback_rev,'foundation_other_checkout_clean':fallback_clean,'mathlib_manifest_revision':mathlib_manifest,'mathlib_checkout_revision':mathlib_rev,'source_only_route_to_missing_mathlib_module':route+['Mathlib.Tactic.Omega'],'mathlib_omega_expected_olean_present':(mathlib/'.lake/build/lib/lean/Mathlib/Tactic/Omega.olean').is_file(),'lean_omega_source_present':(local_roots['Lean']/'Lean/Elab/Tactic/Omega.lean').is_file(),'scope':'Presence, source bytes, configured source roots and selected checkout revisions only; no source substitution, Lean/provider selection, build, transitive frontier or theorem validation.'},sort_keys=True,indent=2))
