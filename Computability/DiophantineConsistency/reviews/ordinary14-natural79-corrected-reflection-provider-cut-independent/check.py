#!/usr/bin/env python3
"""Independent bounded BFS and collision review; no Lean or writes."""
from pathlib import Path
from collections import deque
import hashlib,json,os,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];R=D/'research';O=R/'ordinary14-natural79-combined-slim-overlay';P=R/'ordinary14-natural79-corrected-reflection-provider-cut';PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');P72=Path('/tmp/p72-current-base-extension-attempt02-20261105/lib')
def sha(x):return hashlib.sha256(x).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(p,sha(b));return b
obs=json.loads(pin(P/'observation.json','5e191072e4760cf91e97524e0d26f9805ef6a7c0b35b2b63e684222e40d5bff7'))
pin(P/'inspect.py','b4d0ed98d712b6edfe67e6242f5a85982096b256be337fcfce7bdebfb666b63a')
inv=json.loads(pin(O/'inventory.json','7f8f722c1a96194dc453a797a2ffafbcfea614b2c8c83fda9a51daefb0558483'))
old=json.loads(pin(R/'ordinary14-natural79-dvd-reflection-slim-draft/result.json','6ee95a0db3f72c4b49199e301f1f63812e9723b0e55ac8af3662e87722599ea6'))
oldcut=json.loads(pin(R/'ordinary14-natural79-qualified-provider-cut/observation.json','c978df77d6a2c68947f827a31e45ede8070b5b76cd26c7eab2306811d6b2610c'))
client=pin(R/'ordinary14-natural79-zero-w-divisibility-client-draft/Natural79ZeroWDivisibility.lean','5166f77208e4af6ed8214663aa3b07550f86796f7183c46e0f1039b0d87c4293').decode()
alt=pin(R/'ordinary14-natural79-dvd-reflection-slim-draft/Natural79ZeroWDivisibility.lean.src','4ab36ba289a4cfce93d80bcc6bcb2cc75f0ca2a64d0a729b076846775dac0896').decode()
helper=pin(R/'ordinary14-natural79-slim-reflection-import-repair/NaturalDvdReflectionSlim.lean.src','90acd025abeaf3e687a28e1e4d2c8695f8443340848430419e3057c4c7ff33f4').decode()
orig=pin(R/'ordinary14-natural79-dvd-reflection-slim-draft/NaturalDvdReflectionSlim.lean','460a52783433fa02c1e9a695e69dcfb8d5c839e3d82d4d26df68816aa67c1ceb').decode()
assert helper=='import Foundation.FirstOrder.Arithmetic.IOpen.Basic\n'+orig
ai='import DiophantineConsistency.BFS943.Direct80NaturalProjection';bi='import NaturalDvdReflectionSlim';ar='TenPositive80NaturalProjection.natural_dvd_of_signed';br='NaturalDvdReflectionSlimDraft.natural_dvd_of_signed'
assert client.count(ai)==client.count(ar)==1 and alt==client.replace(ai,bi).replace(ar,br)
def imports(s):
 out=[]
 for line in s.splitlines():
  t=line.strip()
  if not t:continue
  if not t.startswith('import '):break
  assert re.fullmatch(r'import\s+[A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*',t)
  out+=t.split()[1:]
 return out
rows={r['module']:r for r in inv['drafts_topological']}; assert len(rows)==195
seeds=set(imports(helper))
for n,row in rows.items():
 text=pin(O/row['overlay_path'],row['overlay_sha256']).decode()
 if n=='Natural79ZeroWDivisibility': assert text==client; text=alt
 seeds.update(x for x in imports(text) if '.' in x)
assert len(seeds)==44
queue=deque(sorted(seeds));seen=set();sources={};front={};external={}
while queue:
 n=queue.popleft()
 if n in seen:continue
 seen.add(n)
 if not n.startswith('DiophantineConsistency.'):
  p=PKG/(n.replace('.','/')+'.olean');external[n]={'path':str(p),'present':p.is_file(),'sha256':sha(p.read_bytes()) if p.is_file() else None};continue
 p=D/'Lean'/(n.replace('.','/')+'.lean');raw=p.read_bytes();obj=P72/(n.replace('.','/')+'.olean')
 if obj.is_file():front[n]={'source_sha256':sha(raw),'object_path':str(obj),'object_sha256':sha(obj.read_bytes())}
 else:
  deps=imports(raw.decode());sources[n]={'path':str(p.relative_to(D)),'sha256':sha(raw),'lexical_imports':deps};queue.extend(deps)
assert sources==obs['projected_source_candidates']==old['projected_source_candidates']
assert front==obs['projected_project_frontier']==old['projected_project_frontier']
new='Foundation.FirstOrder.Arithmetic.IOpen.Basic'
assert len(sources)==5 and len(front)==41 and len(external)==6 and all(x['present'] for x in external.values())
assert external==obs['projected_external'] and set(external)==set(old['projected_external'])|{new}
source=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Arithmetic/IOpen/Basic.lean')
pin(source,'4ec52a7a487aeafb0e9ea10716452b34f138d8214ad5a1aa5466064d6a4c9d7b')
assert external[new]['sha256']=='fdf05f04ff241ddea16128e1fc799cc5cc9470fbc1a63c92a200688ee597ef45'
scan=obs['proposed_output_collision_scan']; roots=oldcut['collision_scan']['roots'];suffixes=oldcut['collision_scan']['suffixes'];names=sorted(set(rows)|set(sources)|{'NaturalDvdReflectionSlim'})
assert scan['roots']==roots and scan['suffixes']==suffixes and scan['names']==names and len(names)==201 and len(roots)==8 and len(suffixes)==13
def evidence(p):
 if not p.is_file():return {'path':str(p),'file':False,'symlink':p.is_symlink()}
 return {'path':str(p),'realpath':str(p.resolve(strict=True)),'sha256':sha(p.read_bytes()),'symlink':p.is_symlink()}
def find(ns):
 found=[]
 for label,root in sorted(roots.items()):
  for n in ns:
   for s in suffixes:
    p=Path(root)/(n.replace('.','/')+s)
    if os.path.lexists(p):found.append((label,n,s,evidence(p)))
 return found
hits=find(names)
assert [{'root':r,'module':n,'suffix':s,'evidence':e} for r,n,s,e in hits]==scan['hits']
assert len(hits)==2 and all(n=='DiophantineConsistency.DiscreteOrderedRingFacts' and s=='.olean' for _,n,s,_ in hits)
providers=find([new]); assert [{'root':r,'suffix':s,'evidence':e} for r,n,s,e in providers]==obs['foundation_provider_name_observations']
selected=[e for r,n,s,e in providers if s=='.olean' and r in ('captured_p72_endpoint','guarded_package')];assert len(selected)==2 and selected[0]['realpath']==selected[1]['realpath']
print(json.dumps({'scope':'bounded lexical BFS and filesystem observations, not provider authentication or Lean proof','overlay_headers_checked':len(rows),'direct_qualified':len(seeds),'missing_project_sources':len(sources),'project_frontier_objects':len(front),'external_modules':len(external),'new_foundation_source_sha256':sha(source.read_bytes()),'new_foundation_object_sha256':external[new]['sha256'],'prospective_names':len(names),'roots':len(roots),'suffixes':len(suffixes),'output_hits':len(hits),'foundation_provider_observations':len(providers),'foundation_two_object_realpaths_equal':True},sort_keys=True,indent=2))
