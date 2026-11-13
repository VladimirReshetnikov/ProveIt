#!/usr/bin/env python3
"""Read-only beta-only lexical stage/provider observation, no Lean or launch."""
from pathlib import Path
import hashlib,json,os,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]; O=D/'research/ordinary14-natural79-beta-only-overlay'
PLAN=D/'research/ordinary14-natural79-corrected-ordered-provider-plan/plan.json'
CUT=D/'research/ordinary14-natural79-corrected-reflection-provider-cut/observation.json'
P72=Path('/tmp/p72-current-base-extension-attempt02-20261105/lib')
sha=lambda b:hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(str(p),sha(b));return b
inv=json.loads(pin(O/'inventory.json','62a171aeb4ba22745d0750e6dc4ec2310c43e294f35a4a25a9dfccfafbafa503'))
prior=json.loads(pin(PLAN,'deb0854620b8fb85461df791c545f43c09814b566ec4685517efa1696d46b035'))
cut=json.loads(pin(CUT,'5e191072e4760cf91e97524e0d26f9805ef6a7c0b35b2b63e684222e40d5bff7'))
assert len(inv['drafts_topological'])==195 and len(prior['candidate_stages'])==201
front=prior['selected_project_frontier_sources_and_objects'];ext=prior['selected_external_cut_sources_and_objects']
assert len(front)==41 and len(ext)==6
# Exact saved paths, final-component symlink state, resolved targets and bytes.
def evidence(p):
 if not os.path.lexists(p):return None
 if not p.is_file():return {'path':str(p),'file':False,'symlink':p.is_symlink()}
 return {'path':str(p),'realpath':str(p.resolve(strict=True)),'sha256':sha(p.read_bytes()),'symlink':p.is_symlink()}
for group in (front,ext):
 for n,r in group.items():
  for k in ('source','object'):
   assert evidence(Path(r[k]['path']))==r[k],(n,k)
def imports(p):
 out=[]
 for line in p.read_text().splitlines():
  if not line.strip():continue
  m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',line)
  if not m:break
  out.extend(m.group(1).split())
 return out
stages=[];done=set(front)|set(ext)
oldmissing=[r for r in prior['candidate_stages'] if r['kind']=='qualified-source-candidate']
assert len(oldmissing)==5 and set(r['module'] for r in oldmissing)==set(cut['projected_source_candidates'])
for row in oldmissing:
 n=row['module'];p=D/row['source'];pin(p,row['source_sha256']);deps=imports(p)
 assert deps==row['lexical_imports'] and set(deps)<=done,(n,sorted(set(deps)-done))
 assert not os.path.lexists(P72/(n.replace('.','/')+'.olean')),n
 stages.append(dict(row));done.add(n)
for row in inv['drafts_topological']:
 n=row['module'];p=O/row['overlay_path'];assert p.is_file() and not p.is_symlink();pin(p,row['overlay_sha256'])
 deps=imports(p);assert [x for x in deps if '.' not in x]==row['bare_imports'] and [x for x in deps if '.' in x]==row['qualified_imports']
 assert n not in done and set(deps)<=done,(n,sorted(set(deps)-done))
 stages.append({'module':n,'kind':'bare-inert-overlay','source':str(p.relative_to(D)),
  'source_sha256':row['overlay_sha256'],'lexical_imports':deps,'unreserved_output_name':n+'.olean'})
 done.add(n)
assert len(stages)==200 and stages[-1]['module']=='Natural79Endpoint'
assert len({r['module'] for r in stages})==len({r['unreserved_output_name'] for r in stages})==200
oldrows={r['module']:r for r in prior['candidate_stages']};newrows={r['module']:r for r in stages}
assert set(oldrows)-set(newrows)=={'Natural79ZeroWJPos'} and set(newrows)<=set(oldrows)
changed={n for n in newrows if newrows[n]['source_sha256']!=oldrows[n]['source_sha256']}
assert changed=={'Natural79ZeroWMainNorm','Natural79ZeroWRootCut','Natural79ZeroWDivisibility','Natural79Endpoint'}
scan=cut['proposed_output_collision_scan'];names=sorted(newrows)
assert set(scan['names'])-set(names)=={'Natural79ZeroWJPos'} and len(names)==200
assert len(scan['roots'])==8 and len(scan['suffixes'])==13
hits=[]
for label,root in sorted(scan['roots'].items()):
 for n in names:
  for suffix in scan['suffixes']:
   p=Path(root)/(n.replace('.','/')+suffix)
   if os.path.lexists(p):hits.append({'root':label,'module':n,'suffix':suffix,'evidence':evidence(p)})
assert hits==[h for h in scan['hits'] if h['module'] in newrows]
print(json.dumps({'scope':'no-launch lexical source order and bounded source/object/slot observations; no Lean, provider authentication or build-readiness claim',
 'overlay_inventory_sha256':sha((O/'inventory.json').read_bytes()),'prior_plan_sha256':sha(PLAN.read_bytes()),'prior_cut_sha256':sha(CUT.read_bytes()),
 'omitted_prior_stage':['Natural79ZeroWJPos'],'changed_stage_sources':sorted(changed),'candidate_stages':stages,
 'selected_project_frontier_sources_and_objects':front,'selected_external_cut_sources_and_objects':ext,
 'bounded_collision_scan':{'names':len(names),'roots':scan['roots'],'suffixes':scan['suffixes'],'hits':hits},
 'lean_run':False,'launch_authorized':False},sort_keys=True,indent=2))
