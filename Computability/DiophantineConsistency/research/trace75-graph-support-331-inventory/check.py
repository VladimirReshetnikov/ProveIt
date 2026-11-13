#!/usr/bin/env python3
"""Read-only, capture-relative inventory; no Lean process and no producer inference."""
import hashlib, json, re, subprocess
from pathlib import Path
from collections import Counter, defaultdict

ROOT = Path(__file__).resolve().parents[4]
RESEARCH = ROOT / 'Computability/DiophantineConsistency/research'
PINS = {
 'trace75-graph-support-replay-plan/observations/attempt01/stdout':'a6293d79952afa80ce14d558eb2e363795c1ffff9dc3d0898c23ff3f1ccf04da',
 'trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json':'b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c',
 'ten-positive-80-coherent-rebuild/observations/attempt04/result.json':'e1ccee0f9c5fdc14cde89368925cb56f41d6acbe5c89a41c9e2bab798184582b',
 'direct-bfs-80-coherent-rebuild/observations/attempt01/result.json':'ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559',
 'trace75-bfs-compatible-provider-rebuild/observations/attempt01/result.json':'04cd437011c9a8b753a310da6c7691f229f9758b9050fdba9b61b812697fbc3c',
 'trace75-bfs-compatible-reverse-rebuild/observations/attempt01/result.json':'9cf2209e033a0baeab5e1ecac3c9aee0f13afffade6c6a716a7661eeff17ba49',
 'trace75-bfs-compatible-forward-rebuild/observations/attempt01/result.json':'f8d6388911e101a7dfae2547907bc6f9245950fa953c3a4769eff00c140fc3d8',
 'direct-bfs-80-ipra-serialized-audit/observations/attempt01/result.json':'beca7bfd182f49fb0640ed2b49bff33aa2aa8e1ec09bb1fa1d632b2f06ab9883',
}
def sha(path):
 try: return hashlib.sha256(Path(path).read_bytes()).hexdigest()
 except (FileNotFoundError,IsADirectoryError): return None
def head():return subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
def paths():
 lines=subprocess.check_output(['rg','--files','Computability/DiophantineConsistency','-g','*.lean'],cwd=ROOT,text=True).splitlines()
 return sorted(x for x in lines if '/reviews/' not in x and '/observations/' not in x)
def imports(path):
 # This is deliberately a line-oriented heuristic, not a Lean parser.
 out=[]
 for line in Path(path).read_text(errors='replace').splitlines():
  m=re.match(r'^\s*import\s+([A-Za-z0-9_.]+)\s*(?:--.*)?$',line)
  if m:out.append(m.group(1))
 return sorted(set(out)-{'Init'})
start=head(); initial_paths=paths(); loaded={}
for rel,expected in PINS.items():
 p=RESEARCH/rel
 assert sha(p)==expected,(rel,sha(p))
 loaded[rel]=json.loads(p.read_text())
plan=loaded[next(iter(PINS))]
final=loaded['trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json']
serial=loaded['direct-bfs-80-ipra-serialized-audit/observations/attempt01/result.json']
project=final['selected_project']; outside=final['selected_outside']; headers=final['serialized_headers']
cone=set(plan['reverse_reachable']); roots={x['module']:x for x in plan['sources']}
assert len(cone)==331 and len(roots)==28 and set(roots)<=cone
edges={(n,d) for n in cone for d in headers[n] if d in cone}
external_project={d for n in cone for d in headers[n] if d in project and d not in cone}
external_outside={d for n in cone for d in headers[n] if d in outside}
assert all(d in project or d in outside for n in cone for d in headers[n])
assert (len(edges),len(external_project),len(external_outside))==(635,71,4)
incoming={n:sum(1 for a,b in edges if a==n) for n in cone};children=defaultdict(list)
for a,b in edges:children[b].append(a)
ready=sorted(n for n in cone if not incoming[n]);order=[]
while ready:
 n=ready.pop(0);order.append(n)
 for c in sorted(children[n]):
  incoming[c]-=1
  if incoming[c]==0:ready.append(c);ready.sort()
assert len(order)==331
runs=list(PINS)[2:7]+[list(PINS)[1]]
exact=defaultdict(list);boundary_exact=defaultdict(list)
for rel in runs:
 data=loaded[rel];assert data['status']=='PASS'
 for s in data['stages']:
  n=s['module']
  if n not in cone | external_project:continue
  obj=(s.get('object') or s['output'])['.olean'];sel=project[n]['.olean']
  if obj['resolved']!=sel['resolved'] or obj['sha256']!=sel['sha256']:continue
  idx=s['index'];obs=(RESEARCH/rel).parent
  if 'ten-positive-80-' in rel: stdout=obs/f'stage-{idx:03d}.stdout';stderr=obs/f'stage-{idx:03d}.stderr'
  elif 'direct-bfs-80-' in rel:stdout=obs/f'stage-{idx:03d}'/'stdout';stderr=obs/f'stage-{idx:03d}'/'stderr'
  else:stdout=obs/f'stage-{idx:02d}.stdout';stderr=obs/f'stage-{idx:02d}.stderr'
  src=Path(s['command'][5]);assert s['exit']==0 and s['status'] in ('PASS','RETURNED')
  (exact if n in cone else boundary_exact)[n].append({'record':rel,'index':idx,'status':s['status'],'exit':s['exit'],'source':str(src),'source_expected':s['source_sha256'],'source_current':sha(src),'stdout':str(stdout),'stdout_expected':s['stdout_sha256'],'stdout_current':sha(stdout),'stderr':str(stderr),'stderr_expected':s['stderr_sha256'],'stderr_current':sha(stderr)})
assert not set(exact)&set(roots) and len(exact)==80 and all(len(v)==1 for v in exact.values())
bybasename=defaultdict(list)
for path in initial_paths:bybasename[Path(path).name].append(path)
remaining=cone-set(roots)-set(exact);assert len(remaining)==223
candidates={}
for n in sorted(remaining):
 wanted=sorted(set(headers[n])-{'Init'})
 matches=[]
 for rel in bybasename[n.split('.')[-1]+'.lean']:
  p=ROOT/rel
  if imports(p)==wanted:matches.append({'path':str(p),'sha256':sha(p)})
 candidates[n]=matches
supplementary={
 'CompactRankVariationRetry': ['/tmp/ipra-compact44-symbolic-unit-join/src/CompactRankVariationRetry.lean','Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-conditional-rank-variation-prototype/CompactRankVariation.lean'],
 'DiophantineConsistency.OldWordIdentification':['/tmp/ipra-marked-suffix-final-build-01/frozen/DiophantineConsistency/OldWordIdentification.lean','Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-local-compact-word-prototype/OldWordIdentification-DRAFT.lean']}
extras={n:[{'path':str(ROOT/p) if not p.startswith('/') else p,'sha256':sha(ROOT/p)} for p in ps] for n,ps in supplementary.items()}
boundary_candidates={}
for n in sorted(external_project):
 wanted=sorted(set(headers[n])-{'Init'})
 boundary_candidates[n]=[{'path':str(ROOT/rel),'sha256':sha(ROOT/rel)} for rel in bybasename[n.split('.')[-1]+'.lean'] if imports(ROOT/rel)==wanted]
receipts={}
for n in sorted(remaining | external_project):
 entries=[]
 for r in serial['producer_direct'].get(n,[]):
  p=r['receipt']; entries.append({'path':p,'recorded_sha256':r['receipt_sha256'],'current_sha256':sha(p),'direct_imports_compared':r['direct_imports_compared']})
 if entries:receipts[n]=entries
bundles={}
for n in sorted(cone|external_project|external_outside):
 record=project.get(n) or outside[n]
 bundles[n]={k:None if v is None else {'resolved':v['resolved'],'recorded_sha256':v['sha256'],'current_sha256':sha(v['resolved'])} for k,v in record.items()}
for n,r in roots.items():
 assert sha(r['source'])==r['source_sha256']
for n,cs in extras.items(): assert cs[0]['sha256'] and cs[0]['sha256']==cs[1]['sha256']
assert head()==start and paths()==initial_paths
hist=Counter(map(len,candidates.values()))
print(json.dumps({'status':'PASS','scope':'Read-only inventory of captured direct graph; candidate source, receipt, object and header coincidences do not authenticate source-to-object production or complete ancestry. Dynamic imports and source identification beyond this bounded scan remain unverified.','head':start,'inputs':PINS,'rg_path_count':len(initial_paths),'rg_paths_sha256':hashlib.sha256(('\n'.join(initial_paths)+'\n').encode()).hexdigest(),'summary':{'cone':len(cone),'roots':len(roots),'exact_recorded_selected':len(exact),'other':len(remaining),'candidate_histogram':dict(sorted(hist.items())),'candidate_receipt_modules':len(set(receipts)&remaining),'candidate_receipt_records':sum(len(receipts[n]) for n in set(receipts)&remaining),'boundary_exact_modules':len(boundary_exact),'boundary_candidate_histogram':dict(sorted(Counter(map(len,boundary_candidates.values())).items())),'boundary_candidate_receipt_modules':len(set(receipts)&external_project),'boundary_candidate_receipt_records':sum(len(receipts[n]) for n in set(receipts)&external_project),'internal_edges':len(edges),'outside_project':len(external_project),'outside_packages':len(external_outside),'bundles_with_any_drift':sum(any(v and v['recorded_sha256']!=v['current_sha256'] for v in b.values()) for b in bundles.values())},'order':order,'internal_edges':sorted(edges),'direct_outside_project':sorted(external_project),'direct_outside_packages':sorted(external_outside),'roots':roots,'exact_selected_stages':exact,'basename_header_candidates':candidates,'supplementary_sources':extras,'candidate_receipts':receipts,'boundary_exact_selected_stages':boundary_exact,'boundary_basename_header_candidates':boundary_candidates,'selected_bundles':bundles},sort_keys=True,indent=2))
