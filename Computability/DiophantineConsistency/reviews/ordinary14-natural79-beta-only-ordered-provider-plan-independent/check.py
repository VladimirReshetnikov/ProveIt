#!/usr/bin/env python3
"""Independent bounded provider/order/collision observation; no Lean."""
from pathlib import Path
import hashlib,json,os,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];O=D/'research/ordinary14-natural79-beta-only-overlay';base=Path('/tmp/p72-current-base-extension-attempt02-20261105/lib')
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(p,sha(b));return b
N=json.loads(pin(D/'research/ordinary14-natural79-beta-only-ordered-provider-plan/plan.json','c28cf9a7ce85ccdad76bbc59b149c9c51c8b8e351aa9def37a2bf02555a989ea'))
P=json.loads(pin(D/'research/ordinary14-natural79-corrected-ordered-provider-plan/plan.json','deb0854620b8fb85461df791c545f43c09814b566ec4685517efa1696d46b035'))
I=json.loads(pin(O/'inventory.json','62a171aeb4ba22745d0750e6dc4ec2310c43e294f35a4a25a9dfccfafbafa503'))
C=json.loads(pin(D/'research/ordinary14-natural79-corrected-reflection-provider-cut/observation.json','5e191072e4760cf91e97524e0d26f9805ef6a7c0b35b2b63e684222e40d5bff7'))
stages=N['candidate_stages'];prev=P['candidate_stages'];assert len(stages)==200 and len(prev)==201 and len(I['drafts_topological'])==195
assert stages[:5]==[r for r in prev if r['kind']=='qualified-source-candidate']
assert {r['module'] for r in stages[:5]}==set(C['projected_source_candidates'])
assert [r['module'] for r in stages[5:]]==[r['module'] for r in I['drafts_topological']]
new={r['module']:r for r in stages};old={r['module']:r for r in prev};assert len(new)==200 and len(old)==201
assert set(old)-set(new)=={'Natural79ZeroWJPos'} and set(new)<set(old)
changed={n for n in new if new[n]['source_sha256']!=old[n]['source_sha256']}
assert changed=={'Natural79ZeroWMainNorm','Natural79ZeroWRootCut','Natural79ZeroWDivisibility','Natural79Endpoint'}
assert sorted(changed)==N['changed_stage_sources'] and N['omitted_prior_stage']==['Natural79ZeroWJPos']
front=N['selected_project_frontier_sources_and_objects'];ext=N['selected_external_cut_sources_and_objects']
assert front==P['selected_project_frontier_sources_and_objects'] and ext==P['selected_external_cut_sources_and_objects']
assert len(front)==41 and len(ext)==6 and not (set(front)&set(ext))
assert 'Foundation.FirstOrder.Arithmetic.IOpen.Basic' in ext
# Re-observe each saved frontier path, including final symlink status and target.
for group in (front,ext):
 for n,r in group.items():
  for typ in ('source','object'):
   record=r[typ];p=Path(record['path'])
   assert p.is_file() and p.is_symlink()==record['symlink']
   assert str(p.resolve(strict=True))==record['realpath']
   pin(p,record['sha256'])
known=set(front)|set(ext);outnames=set();source_by_module={r['module']:r for r in I['drafts_topological']}
for i,r in enumerate(stages):
 n=r['module'];assert n not in known
 p=D/r['source'];data=pin(p,r['source_sha256']);assert p.is_file() and not p.is_symlink()
 if i<5:assert not os.path.lexists(base/(n.replace('.','/')+'.olean'))
 else:
  selected=source_by_module[n];assert data==pin(O/selected['overlay_path'],selected['overlay_sha256'])
 imps=[]
 for line in data.decode().splitlines():
  if not line.strip():continue
  if not line.startswith('import '):break
  assert re.fullmatch(r'import\s+[A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*\s*',line),line
  imps.extend(line.split()[1:])
 assert imps==r['lexical_imports'] and set(imps)<=known,(n,sorted(set(imps)-known))
 out=r['unreserved_output_name'];assert out not in outnames;outnames.add(out);known.add(n)
assert stages[-1]['module']=='Natural79Endpoint'
# A bounded slot observation, including broken symlinks, with exact recorded roots/suffixes.
scan=N['bounded_collision_scan'];prior_scan=C['proposed_output_collision_scan']
assert scan['roots']==prior_scan['roots'] and scan['suffixes']==prior_scan['suffixes']
assert len(scan['roots'])==8 and len(scan['suffixes'])==13 and scan['names']==200
hits=[]
for label,root in sorted(scan['roots'].items()):
 for n in sorted(new):
  for suffix in scan['suffixes']:
   p=Path(root)/(n.replace('.','/')+suffix)
   if not os.path.lexists(p):continue
   if p.is_file():ev={'path':str(p),'realpath':str(p.resolve(strict=True)),'sha256':sha(p.read_bytes()),'symlink':p.is_symlink()}
   else:ev={'path':str(p),'file':False,'symlink':p.is_symlink()}
   hits.append({'root':label,'module':n,'suffix':suffix,'evidence':ev})
assert hits==scan['hits'] and len(hits)==2
assert all(x['module']=='DiophantineConsistency.DiscreteOrderedRingFacts' and x['suffix']=='.olean' for x in hits)
assert {x['root'] for x in hits}=={'captured_p72_endpoint','carrier_retry05'}
assert N['lean_run'] is False and N['launch_authorized'] is False
print(json.dumps({'scope':'bounded read-only source/order/frontier and collision observation; no Lean/provider proof',
 'stages':200,'qualified_candidates':5,'beta_only_overlay_stages':195,'omitted':'Natural79ZeroWJPos',
 'changed_sources':sorted(changed),'project_frontier_records':41,'external_frontier_records':6,
 'observed_output_names':200,'collision_roots':8,'collision_suffixes':13,'collision_hits':2,
 'lean_executed':False,'launch_authorized':False},sort_keys=True,indent=2))
