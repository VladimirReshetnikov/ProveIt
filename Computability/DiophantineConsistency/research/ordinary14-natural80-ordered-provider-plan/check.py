#!/usr/bin/env python3
"""Rebuild an inert lexical candidate plan; never invokes Lean or writes files."""
import hashlib,json,os,re,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
OVERLAY=D/'research/ordinary14-natural80-combined-slim-overlay'
CUT=D/'research/ordinary14-natural80-qualified-provider-cut/observation.json'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(path,h):
 data=path.read_bytes();assert sha(data)==h,(str(path),sha(data));return json.loads(data)
inv=pin(OVERLAY/'inventory.json','bd10f4c2b320ce1255f57f5bf1e9aefc346d2b2a2b5a8b989547f78f060c2be7')
cut=pin(CUT,'c88630304b866b29fe68a11f14f44af210fcd8ea5eed173523ae687c8c157979')
front=cut['selected_project_frontier']; external=cut['selected_external']; new=cut['source_candidates']
assert len(front)==40 and len(external)==4 and len(new)==5 and len(inv['drafts_topological'])==184
expected=set(['DiophantineConsistency.BFS943.Direct80IndexOne','DiophantineConsistency.Compact44.FreeJ13','DiophantineConsistency.Compact44.FreeJ13Halt','DiophantineConsistency.DiscreteOrderedRingFacts','DiophantineConsistency.HAExpressionNoZeroEquiv'])
assert set(new)==expected
# Every observation is checked at its selected path, including symlink status,
# target identity and bytes; this is not an authenticated producer history.
def evidence(path):
 if not os.path.lexists(path):return None
 if not path.is_file():return {'path':str(path),'file':False,'symlink':path.is_symlink()}
 return {'path':str(path),'realpath':str(path.resolve(strict=True)),'sha256':sha(path.read_bytes()),'symlink':path.is_symlink()}
for n,row in front.items():
 item=row['object'];assert evidence(Path(item['path']))==item,n
 data=(D/row['current_source_path']).read_bytes();assert sha(data)==row['current_source_sha256'],n
for n,item in external.items(): assert evidence(Path(item['path']))==item,n

def imports(path):
 out=[]
 for line in path.read_text().splitlines():
  line=line.strip()
  if not line:continue
  if not line.startswith('import '):break
  assert re.fullmatch(r'import [A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*',line),(str(path),line)
  out.extend(line.split()[1:])
 return out
# One specific order of the five missing source candidates. This only orders
# the lexical headers against the observed frontier; it is not lean --deps.
first=['DiophantineConsistency.DiscreteOrderedRingFacts','DiophantineConsistency.Compact44.FreeJ13','DiophantineConsistency.Compact44.FreeJ13Halt','DiophantineConsistency.BFS943.Direct80IndexOne','DiophantineConsistency.HAExpressionNoZeroEquiv']
assert set(first)==set(new)
done=set(front)|set(external);stages=[]
for name in first:
 row=new[name];source=D/row['path'];assert sha(source.read_bytes())==row['sha256']
 deps=imports(source);assert deps==row['lexical_imports'] and set(deps)<=done,(name,set(deps)-done)
 stages.append({'module':name,'kind':'qualified-source-candidate','source':row['path'],
  'source_sha256':row['sha256'],'lexical_imports':deps,'unreserved_output_name':name.replace('.','/')+'.olean'})
 done.add(name)
for row in inv['drafts_topological']:
 name=row['module'];source=OVERLAY/row['overlay_path'];data=source.read_bytes()
 assert source.is_file() and not source.is_symlink() and sha(data)==row['overlay_sha256'],name
 deps=imports(source);assert [x for x in deps if '.' not in x]==row['bare_imports'] and [x for x in deps if '.' in x]==row['qualified_imports']
 assert name not in done and set(deps)<=done,(name,set(deps)-done)
 stages.append({'module':name,'kind':'bare-inert-overlay','source':str(source.relative_to(D)),
  'source_sha256':row['overlay_sha256'],'lexical_imports':deps,'unreserved_output_name':name+'.olean'})
 done.add(name)
assert len(stages)==189 and stages[-1]['module']=='Natural80Endpoint'
# Repeat exactly the prior 189-name/eight-root/13-suffix collision observation.
# These named roots are not a complete global search or future output root.
scan=cut['collision_scan']; names=sorted({r['module'] for r in inv['drafts_topological']}|set(new));assert len(names)==scan['names']==189
hits=[]
for label,root in scan['roots'].items():
 for name in names:
  for suffix in scan['suffixes']:
   p=Path(root)/(name.replace('.','/')+suffix)
   if os.path.lexists(p):hits.append({'root':label,'module':name,'suffix':suffix,'evidence':evidence(p)})
# Match records ignoring JSON key order, preserving the original traversal set.
key=lambda x:(x['root'],x['module'],x['suffix'])
assert sorted(hits,key=key)==sorted(scan['hits'],key=key)
print(json.dumps({'scope':'bounded ordered lexical source candidate and sampled object/slot observations; no Lean, full provider closure or build-readiness claim',
 'overlay_inventory_sha256':sha((OVERLAY/'inventory.json').read_bytes()),'provider_cut_sha256':sha(CUT.read_bytes()),
 'candidate_stages':stages,'selected_project_frontier_objects':{n:front[n]['object'] for n in sorted(front)},
 'selected_external_cut_objects':{n:external[n] for n in sorted(external)},
 'bounded_collision_scan':{'names':len(names),'roots':scan['roots'],'suffixes':scan['suffixes'],'hits':hits}},sort_keys=True,indent=2))
