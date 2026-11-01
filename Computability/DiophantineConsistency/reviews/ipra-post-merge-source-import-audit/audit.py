#!/usr/bin/env python3
"""Read-only source-import intersection audit; no object validation."""
import hashlib,json,re,subprocess
from pathlib import Path
root=Path(__file__).resolve().parents[4]
roots=[root/'Computability/DiophantineConsistency/Lean',root/'Logic/Interpretability/ZFCinPA/Lean',Path('/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation')]
commit='69ca27250b'; names=['IPRANativeInduction','IPRAInductionNativeGG','IPRANativeTheory','IPRANativeBasicImages','IPRAEqualitySymmetryGG','IPRABinaryRelationNative','IPRAConditionalComparison']
changed=sorted(subprocess.check_output(['git','diff','--name-only',commit+'^1',commit],cwd=root,text=True).splitlines())
sh=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
res={'scope':'Source-import intersection only; no object coherence, package transitive closure, or build verification.','commit':commit,'first_parent':subprocess.check_output(['git','rev-parse',commit+'^1'],cwd=root,text=True).strip(),'changed_files':changed,'targets':{}}
for name in names:
 stack=['DiophantineConsistency.'+name];seen={};missing=[];hits=[];external=set()
 while stack:
  x=stack.pop()
  if x in seen:continue
  rel=Path(*x.split('.')).with_suffix('.lean');p=next((r/rel for r in roots if (r/rel).is_file()),None)
  if p is None:seen[x]=None;missing.append(x);continue
  try: label=str(p.relative_to(root))
  except ValueError:label=str(p)
  seen[x]={'path':label,'sha256':sh(p)}
  if label in changed:hits.append(label)
  for line in p.read_text(errors='replace').splitlines():
   match=re.match(r'^\s*(?:public\s+)?import\s+(.+?)(?:\s*--.*)?$',line)
   if not match:continue
   for im in match.group(1).split():
    if not re.fullmatch(r'[A-Za-z0-9_\.]+',im):continue
    if im.startswith(('DiophantineConsistency.','ZFCinPA.','Foundation.')):stack.append(im)
    else:external.add(im)
 res['targets'][name]={'resolved_sources':dict(sorted(seen.items())),'missing_local_modules':sorted(missing),'changed_in_closure':sorted(hits),'untraversed_package_imports':sorted(external)}
assert all(not v['missing_local_modules'] and not v['changed_in_closure'] for v in res['targets'].values())
p=Path(__file__).resolve().parent/'receipt.json';p.write_text(json.dumps(res,indent=2)+'\n');print('PASS',len(changed),'changed files; '+'; '.join(f'{k}: {len(v["resolved_sources"])} sources, 0 intersect' for k,v in res['targets'].items()))
