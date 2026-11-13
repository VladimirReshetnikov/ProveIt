#!/usr/bin/env python3
"""Independent check of lexical order and observed files; no Lean or writes."""
from pathlib import Path
import hashlib,json,os,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];R=D/'research';P=R/'ordinary14-natural79-corrected-ordered-provider-plan';O=R/'ordinary14-natural79-corrected-reflection-overlay'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(path,h):
 b=path.read_bytes();assert sha(b)==h,(str(path),sha(b));return b
plan=json.loads(pin(P/'plan.json','deb0854620b8fb85461df791c545f43c09814b566ec4685517efa1696d46b035'))
pin(P/'check.py','608eeb63416f4a08cbbe131ef8c5bc868831574c9321cf1bd2125fb9435dc61e')
inv=json.loads(pin(O/'inventory.json','fc9da87f4178c7f3b06c549a792f7e80baac2217a6735bcb38e49b280a90d434'))
cut=json.loads(pin(R/'ordinary14-natural79-corrected-reflection-provider-cut/observation.json','5e191072e4760cf91e97524e0d26f9805ef6a7c0b35b2b63e684222e40d5bff7'))
prior=json.loads(pin(R/'ordinary14-natural79-qualified-provider-cut/observation.json','c978df77d6a2c68947f827a31e45ede8070b5b76cd26c7eab2306811d6b2610c'))
assert plan['overlay_inventory_sha256']=='fc9da87f4178c7f3b06c549a792f7e80baac2217a6735bcb38e49b280a90d434' and plan['provider_cut_sha256']=='5e191072e4760cf91e97524e0d26f9805ef6a7c0b35b2b63e684222e40d5bff7'
def imports(raw):
 out=[]
 for line in raw.decode().splitlines():
  text=line.strip()
  if not text:continue
  if not text.startswith('import '):break
  assert re.fullmatch(r'import\s+[A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*',text),text
  out.extend(text.split()[1:])
 return out
def evidence(p):
 if not p.is_file():return {'path':str(p),'file':False,'symlink':p.is_symlink()}
 return {'path':str(p),'realpath':str(p.resolve(strict=True)),'sha256':sha(p.read_bytes()),'symlink':p.is_symlink()}
front=cut['projected_project_frontier'];ext=cut['projected_external'];missing=cut['projected_source_candidates'];stages=plan['candidate_stages']; old=inv['drafts_topological']
assert (len(stages),len(missing),len(front),len(ext),len(old))==(201,5,41,6,196)
project=plan['selected_project_frontier_sources_and_objects'];external=plan['selected_external_cut_sources_and_objects'];assert set(project)==set(front) and set(external)==set(ext)
for n,record in project.items():
 oldrec=prior['selected_project_frontier'][n];obj=record['object'];source=record['source']
 assert evidence(Path(source['path']))==source and evidence(Path(obj['path']))==obj
 assert source['sha256']==front[n]['source_sha256']==oldrec['current_source_sha256'] and obj==oldrec['object'] and obj['sha256']==front[n]['object_sha256']
 for k in ('p72_snapshot_source_sha256','base_record_source_sha256','base_record_object_sha256'):assert record[k]==oldrec[k]
for n,record in external.items():
 for typ in ('source','object'):assert evidence(Path(record[typ]['path']))==record[typ]
 assert record['object']['path']==ext[n]['path'] and record['object']['sha256']==ext[n]['sha256'] and ext[n]['present']
 if n.startswith('Foundation.'):assert record['source']==cut['foundation_source']
assert [x['module'] for x in stages[5:]]==[x['module'] for x in old]
seen=set(front)|set(ext); outputs=set()
for i,row in enumerate(stages):
 n=row['module'];assert n not in seen
 p=D/row['source'];raw=pin(p,row['source_sha256']);deps=imports(raw)
 assert deps==row['lexical_imports'] and set(deps)<=seen,(i,n,set(deps)-seen)
 if i<5:
  assert row['kind']=='qualified-source-candidate' and n in missing
  rec=missing[n];assert row['source']==rec['path'] and row['source_sha256']==rec['sha256'] and deps==rec['lexical_imports']
  expected=n.replace('.','/')+'.olean'
 else:
  rec=old[i-5];assert row['kind']=='bare-inert-overlay' and not p.is_symlink()
  assert p==O/rec['overlay_path'] and row['source_sha256']==rec['overlay_sha256']
  assert [d for d in deps if '.' not in d]==rec['bare_imports'] and [d for d in deps if '.' in d]==rec['qualified_imports']
  expected=n+'.olean'
 assert row['unreserved_output_name']==expected and expected not in outputs
 outputs.add(expected);seen.add(n)
assert {r['module'] for r in stages[:5]}==set(missing) and stages[-1]['module']=='Natural79Endpoint'
scan=cut['proposed_output_collision_scan']; names=sorted(r['module'] for r in stages);roots=scan['roots'];suffixes=scan['suffixes'];assert names==scan['names'] and (len(names),len(roots),len(suffixes))==(201,8,13)
hits=[]
for name in names:
 for label,root in roots.items():
  for suffix in suffixes:
   p=Path(root)/(name.replace('.','/')+suffix)
   if os.path.lexists(p):hits.append({'root':label,'module':name,'suffix':suffix,'evidence':evidence(p)})
hits.sort(key=lambda x:(x['root'],x['module'],suffixes.index(x['suffix'])))
assert hits==scan['hits']==plan['bounded_collision_scan']['hits'] and len(hits)==2
assert plan['bounded_collision_scan']['roots']==roots and plan['bounded_collision_scan']['suffixes']==suffixes and plan['bounded_collision_scan']['names']==201
print(json.dumps({'scope':'pinned simple source headers, lexical order and bounded file observations only; no Lean, provider authentication or build-readiness claim','stage_count':len(stages),'initial_candidates':5,'overlay_snapshots':196,'unique_primary_outputs':len(outputs),'frontier_project_records':len(project),'external_records':len(external),'collision_slot_count':len(names)*len(roots)*len(suffixes),'collision_hits':len(hits),'last_module':stages[-1]['module']},indent=2,sort_keys=True))
