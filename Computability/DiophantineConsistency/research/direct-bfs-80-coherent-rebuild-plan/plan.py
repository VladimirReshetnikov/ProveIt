#!/usr/bin/env python3
"""Read-only, capture-relative dependency plan; this does not run Lean."""
from pathlib import Path
from hashlib import sha256
from collections import deque
import json, re
H=Path(__file__).resolve().parent
D=H.parents[1]
inputs={
 'fixed_capture':(D/'research/direct-bfs-80-ipra-serialized-audit/observations/attempt01/result.json','beca7bfd182f49fb0640ed2b49bff33aa2aa8e1ec09bb1fa1d632b2f06ab9883'),
 'rebuilt_capture':(D/'reviews/ten-positive-80-coherent-rebuilt-closure/observations/attempt01/result.json','75d4cf43ed4d716b15a13536be5a4cbba96ad03e2249aba7acdc7ace30892276'),
 'rebuilt_run':(D/'research/ten-positive-80-coherent-rebuild/observations/attempt04/result.json','e1ccee0f9c5fdc14cde89368925cb56f41d6acbe5c89a41c9e2bab798184582b'),
 'old_negative_state':(H/'evidence/old-negative-state.json','84c3bc6f6c34c47e67278c43df8580444d32e2946844a4c40c31cfd747f33a90'),
 'old_ratio_receipt':(H/'evidence/old-ratio-receipt.json','1f7bad2e931bbfe6730e03be7b8963ac746b5bb76f44c7c6ebecaf238b35fc6e'),
 'old_negative_source':(H/'evidence/ArithmeticNegativeNorms.lean','00c0a3b6bbddd9d6ea23d1e1ecbcc2e02f383a76e7618f6328288d413719d7ef'),
 'old_ratio_source':(H/'evidence/ModelRatioBounds.lean','8ad9d28011406f9a8f2f6e8658405b4e582a7bdd224c83d2a2eb893a81116046'),
}
def sha(p):return sha256(p.read_bytes()).hexdigest()
def need(b,s):
 if not b:raise RuntimeError(s)
for n,(p,h) in inputs.items():need(sha(p)==h,'input drift '+n)
a=json.loads(inputs['fixed_capture'][0].read_text());b=json.loads(inputs['rebuilt_capture'][0].read_text());run=json.loads(inputs['rebuilt_run'][0].read_text());neg=json.loads(inputs['old_negative_state'][0].read_text());ratio=json.loads(inputs['old_ratio_receipt'][0].read_text())
need(a['status']=='PASS_CAPTURE' and b['status']=='PASS' and run['status']=='PASS','input status')
P=a['closure']['project'];O=a['closure']['outside'];B=b['selected_project'];stages={s['module']:s for s in run['stages']}
seeds=['DiophantineConsistency.ArithmeticNegativeNorms','DiophantineConsistency.ModelRatioBounds']
negrow=next(x for x in neg['records'] if x['module']==seeds[0]);need(negrow['verified'] and negrow['exit']==0,'old negative producer')
need(ratio['status']=='PASS' and ratio['module']==seeds[1],'old ratio producer')
olddeps=[negrow['dependency_hashes'],{n:v['record']['sha256'] for n,v in ratio['direct'].items()}]
oldouts=[negrow['object_sha256'],ratio['output']['sha256']]
sourcehash=[negrow['source_sha256'],ratio['source_sha256']]
foundations=[]
for i,n in enumerate(seeds):
 st=stages[n];old=P[n];new=B[n]
 need(oldouts[i]==old['record']['sha256'] and sourcehash[i]==st['source_sha256'],'old/source/rebuild mismatch '+n)
 need(st['exit']==0 and st['reason'] is None and st['output']['.olean']['sha256']==new['.olean']['sha256'],'rebuild stage mismatch '+n)
 need(old['imports']==b['headers'][n],'different serialized import names '+n)
 selected={};diff={}
 for dep,oldhash in olddeps[i].items():
  cur=P.get(dep,O.get(dep));need(cur is not None,'unresolved selected '+dep)
  selected[dep]=cur['record']['sha256']
  if selected[dep]!=oldhash:diff[dep]={'producer':oldhash,'fixed_selected':selected[dep]}
 foundations.append({'module':n,'old_object':oldouts[i],'new_object':new['.olean']['sha256'],'shared_source':sourcehash[i],
  'old_serialized_imports':old['imports'],'rebuilt_serialized_imports':b['headers'][n],
  'old_producer_direct_hashes':olddeps[i],'fixed_selected_direct_hashes':selected,'producer_direct_drift':diff,'rebuilt_stage_index':st['index']})
need(len(foundations[0]['producer_direct_drift'])==1 and len(foundations[1]['producer_direct_drift'])==3,'unexpected drift classification')
rev={n:set() for n in P}
for n,row in P.items():
 for dep in row['imports']:
  if dep in rev:rev[dep].add(n)
affected=set(seeds);queue=deque(seeds)
while queue:
 for n in sorted(rev[queue.popleft()]):
  if n not in affected:affected.add(n);queue.append(n)
todo=affected-set(B);supplement=set(P)-set(B)-todo
need(len(affected)==84 and len(affected&set(B))==19 and len(todo)==65 and len(supplement)==101,'cone classification changed')
need(all(n in stages and stages[n]['exit']==0 and stages[n]['reason'] is None for n in affected&set(B)),'affected existing modules not in successful 127 replay')
remaining=set(todo);order=[]
while remaining:
 ready=sorted(n for n in remaining if not (set(P[n]['imports']) & remaining))
 need(ready,'cycle in captured project headers')
 order.extend(ready);remaining.difference_update(ready)
records=[]
for idx,n in enumerate(order,1):
 picked=None
 for ref in a['producer_direct'].get(n,[]):
  rp=Path(ref['receipt']);j=json.loads(rp.read_text());sp=rp.parent/'source.txt'
  if not sp.is_file():continue
  source=sha(sp)
  if source!=j.get('pins',{}).get('source'):continue
  imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',sp.read_text(),re.M)
  if imports!=[x for x in P[n]['imports'] if x!='Init']:continue
  if j.get('exit')!=0 or j.get('reason') is not None or j.get('pins')!=j.get('after'):continue
  need(j.get('object_sha256')==P[n]['record']['sha256'],'producer object mismatch '+n)
  picked={'receipt':str(rp),'receipt_sha256':sha(rp),'source_snapshot':str(sp),'source_sha256':source,
   'recorded_direct_import_count':len(j.get('direct_imports',[])),'recorded_direct_comparisons':ref['direct_imports_compared']}
  break
 need(picked is not None,'no verified source snapshot '+n)
 records.append({'index':idx,'module':n,'captured_imports':P[n]['imports'],'dependencies_in_rebuild':sorted(set(P[n]['imports'])&todo),
  'old_selected_object':P[n]['record'],'producer':picked})
result={'scope':'read-only plan relative to the two captured mismatches and serialized import graphs; no rebuild, package-transitive proof or complete historical source ancestry',
 'inputs':{n:{'path':str(p),'sha256':h} for n,(p,h) in inputs.items()},'mismatch_producers':foundations,
 'report':{'affected':len(affected),'affected_already_rebuilt':len(affected&set(B)), 'affected_to_rebuild':len(todo),
  'unaffected_missing_supplements':len(supplement),'stages_with_no_recorded_direct_imports':sum(x['producer']['recorded_direct_import_count']==0 for x in records)},
 'affected_already_rebuilt':sorted(affected&set(B)),'unaffected_missing_supplements':sorted(supplement),'rebuild_order':records}
out=H/'observations/attempt01/result.json';need(not out.exists(),'output exists');out.parent.mkdir(parents=True,exist_ok=True)
for n,(p,h) in inputs.items():need(sha(p)==h,'input drift at end '+n)
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS_PLAN','report':result['report'],'producer_drift':{x['module']:x['producer_direct_drift'] for x in foundations}},indent=2))
