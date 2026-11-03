from pathlib import Path
import hashlib,json,re,subprocess,collections
D=Path(__file__).resolve().parents[2];ROOT=D.parents[1];h=D/'research/trace75-graph-support-331-inventory';o=h/'observations/attempt02';R=D/'research'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
assert sha(h/'check.py')=='9356f8d5668a62c75ef3a61adb9f7708f720aa821a8e6051a1f4554fa97a2ae0' and sha(o/'terminal.json')=='a620170e37b87be9f38b304721d42fec5810ac6b55a60d886abedffc04d047ee' and sha(o/'stdout')=='8a4748cf03711674ff0c1c6d14f7703afbd7f4f08673a2c4aed67ec32822537d';t=load(o/'terminal.json');assert t['exit']==0 and t['checker_sha256_before']==t['checker_sha256_after']==sha(h/'check.py') and t['stdout_sha256']==sha(o/'stdout') and t['stderr_sha256']==sha(o/'stderr');j=load(o/'stdout');assert j['status']=='PASS'
for p,v in j['inputs'].items():assert sha(R/p)==v
plan=load(R/'trace75-graph-support-replay-plan/observations/attempt01/stdout');final=load(R/'trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json');serial=load(R/'direct-bfs-80-ipra-serialized-audit/observations/attempt01/result.json');heads=final['serialized_headers'];project=final['selected_project'];outside=final['selected_outside'];cone=set(plan['reverse_reachable']);roots={x['module']:x for x in plan['sources']};assert len(cone)==331 and len(roots)==28 and roots==j['roots']
edges={(n,d) for n in cone for d in heads[n] if d in cone};up={d for n in cone for d in heads[n] if d in project and d not in cone};ext={d for n in cone for d in heads[n] if d in outside};assert len(edges)==635 and len(up)==71 and len(ext)==4 and [list(x) for x in sorted(edges)]==j['internal_edges'] and sorted(up)==j['direct_outside_project'] and sorted(ext)==j['direct_outside_packages'];assert set(j['order'])==cone and len(j['order'])==331;pos={n:i for i,n in enumerate(j['order'])};assert all(pos[d]<pos[n] for n,d in edges)
assert set(j['selected_bundles'])==cone|up|ext
for n,b in j['selected_bundles'].items():
 selected=project.get(n) or outside[n];assert set(b)==set(selected)
 for k,v in b.items():
  old=selected[k]
  if v is None:assert old is None
  else:assert v['resolved']==old['resolved'] and v['recorded_sha256']==old['sha256']==v['current_sha256']==sha(v['resolved'])
for n,r in roots.items():assert sha(r['source'])==r['source_sha256']
runpaths=['ten-positive-80-coherent-rebuild/observations/attempt04/result.json','direct-bfs-80-coherent-rebuild/observations/attempt01/result.json','trace75-bfs-compatible-provider-rebuild/observations/attempt01/result.json','trace75-bfs-compatible-reverse-rebuild/observations/attempt01/result.json','trace75-bfs-compatible-forward-rebuild/observations/attempt01/result.json','trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json'];runs={p:load(R/p) for p in runpaths};matches={}
for path,r in runs.items():
 assert r['status']=='PASS'
 for stage in r['stages']:
  n=stage['module']
  if n not in cone|up:continue
  obj=(stage.get('object') or stage['output'])['.olean'];sel=project[n]['.olean']
  if obj['resolved']==sel['resolved'] and obj['sha256']==sel['sha256']:
   assert n not in matches;matches[n]=(path,stage)
exact=j['exact_selected_stages'];bexact=j['boundary_exact_selected_stages'];assert set(exact)==set(matches)&cone and set(bexact)==set(matches)&up and len(exact)==80 and len(bexact)==8 and not (set(exact)&set(roots))
for n,obs in {**exact,**bexact}.items():
 assert len(obs)==1;q=obs[0];path,s=matches[n];assert q['record']==path and q['index']==s['index'] and q['status']==s['status'] in ('PASS','RETURNED') and q['exit']==s['exit']==0 and q['source']==s['command'][5] and q['source_expected']==s['source_sha256']==q['source_current']==sha(q['source'])
 for extname in ('stdout','stderr'):assert q[extname+'_expected']==s[extname+'_sha256']==q[extname+'_current']==sha(q[extname])
remaining=cone-set(roots)-set(exact);assert len(remaining)==223;assert set(j['basename_header_candidates'])==remaining and set(j['boundary_basename_header_candidates'])==up
for cat,names in [('basename_header_candidates',remaining),('boundary_basename_header_candidates',up)]:
 for n,items in j[cat].items():
  assert n in names
  for v in items:
   p=Path(v['path']);assert p.name==n.split('.')[-1]+'.lean' and sha(p)==v['sha256'];imports=sorted(set(re.findall(r'^\s*import\s+([A-Za-z0-9_.]+)\s*(?:--.*)?$',p.read_text(errors='replace'),re.M)) - {'Init'});assert imports==sorted(set(heads[n])-{'Init'})
assert collections.Counter(map(len,j['basename_header_candidates'].values()))=={0:2,1:218,2:3} and collections.Counter(map(len,j['boundary_basename_header_candidates'].values()))=={0:1,1:59,2:11}
assert {n for n,x in j['basename_header_candidates'].items() if not x}=={'CompactRankVariationRetry','DiophantineConsistency.OldWordIdentification'};assert [n for n,x in j['boundary_basename_header_candidates'].items() if not x]==['DiophantineConsistency.CompactWordCellClient']
for n,pair in j['supplementary_sources'].items():assert len(pair)==2 and sha(pair[0]['path'])==pair[0]['sha256']==pair[1]['sha256']==sha(pair[1]['path'])
assert sum(len(set(v['sha256'] for v in rows))>1 for rows in j['boundary_basename_header_candidates'].values() if len(rows)==2)==4
receiptmap=j['candidate_receipts'];assert len(set(receiptmap)&remaining)==18 and len(set(receiptmap)&up)==17 and len(set(receiptmap)&up&set(bexact))==3
for n in remaining|up:
 old=serial['producer_direct'].get(n,[]);observed=receiptmap.get(n,[]);assert len(old)==len(observed)
 for a,b in zip(old,observed):assert b['path']==a['receipt'] and b['recorded_sha256']==a['receipt_sha256']==b['current_sha256']==sha(b['path']) and b['direct_imports_compared']==a['direct_imports_compared']
print('PASS captured 331/635/71+4, 406 bundles, 28 root/80+8 exact stages, recorded candidate histograms, 35 receipt groups and 3 overlap; all retained candidate bytes match')
print('captured HEAD',j['head'],'current HEAD',subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip())
