from pathlib import Path
import collections,hashlib,json,re,subprocess
D=Path(__file__).resolve().parents[2]; obs=D/'research/trace75-cone-source-inventory/observations/attempt03'; inv=D/'research/trace75-cone-source-inventory/check.py'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
assert sha(inv)==sha(obs/'source.txt')=='7e17c6d76e6f9baa78779b88b2976487a8cc3553ba906e8ef29a8262f9306e33'
assert sha(obs/'terminal.json')=='92a083a3e5303c190846f3dd0f083eef840b6cb3cd980d0fa05054a22970bcc5'
assert sha(obs/'stdout')=='473df595296a18b16836906d2dd6daf4b740fea1e56014e1bebaaabd9fececbf'
t=load(obs/'terminal.json');assert t['exit']==0 and t['checker_sha256']==sha(inv) and t['stdout_sha256']==sha(obs/'stdout') and t['stderr_sha256']==sha(obs/'stderr')
d=load(obs/'stdout'); final=load(D/'research/trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json'); headers=final['serialized_headers']; records={r['module']:r for r in d['records']};assert len(records)==186
fixed=set(final['closures']['Trace75BFSFixedIPRA']['project']); seeds=set(final['inherited_baseline_four']); assert len(seeds)==4
users=collections.defaultdict(set)
for n in fixed:
 for p in headers[n]:
  if p in fixed:users[p].add(n)
cone=set(seeds);pending=list(seeds)
while pending:
 for x in users[pending.pop()]-cone:cone.add(x);pending.append(x)
assert cone==set(records); upstream=set();outside=set();edges=0
for n in cone:
 for dep in set(headers[n]):
  if dep in cone:edges+=1
  elif dep in final['selected_project']:upstream.add(dep)
  elif dep in final['selected_outside']:outside.add(dep)
  else:raise AssertionError((n,dep))
assert edges==294 and len(upstream)==141 and len(outside)==4 and sorted(upstream)==d['upstream_project'] and sorted(outside)==d['outside_direct']
order=d['topological_order'];assert set(order)==cone and len(order)==len(cone);pos={n:i for i,n in enumerate(order)}
for n in cone:
 for dep in set(headers[n])&cone:assert pos[dep]<pos[n]
gitroot=Path(subprocess.check_output(['git','-C',str(D),'rev-parse','--show-toplevel'],text=True).strip());head=subprocess.check_output(['git','-C',str(D),'rev-parse','HEAD'],text=True).strip();assert head==d['git_head']
tracked=set(subprocess.check_output(['git','-C',str(D),'ls-files','--full-name','-z'],text=True).split('\0'))
plan127=load(D/'reviews/ten-positive-80-127-rebuild-preflight/observations/attempt01.json')['sources'];plan65={x['module']:x['producer'] for x in load(D/'research/direct-bfs-80-coherent-rebuild-plan/observations/attempt01/result.json')['rebuild_order']};cache={};counts=collections.Counter();direct=0;untracked=[]
def hs(x):return {k:(v['sha256'] if v else None) for k,v in x.items()}
for n,r in records.items():
 path=D/r['producer_result'];prod=cache.setdefault(str(path),load(path));s=[s for s in prod['stages'] if s['index']==r['producer_stage']];assert len(s)==1;s=s[0];assert s['module']==n and s['exit']==0 and s['reason'] is None
 out=s.get('object') or s.get('output');chosen=final['selected_project'][n];assert out['.olean']['resolved']==chosen['.olean']['resolved']==r['object_realpath'] and hs(out)==hs(chosen);assert sha(out['.olean']['path'])==r['object_sha256']==out['.olean']['sha256']
 for f in ('copied_source','listed_source','workspace_candidate'):assert sha(r[f])==r['source_sha256']==s['source_sha256']
 assert Path(s['command'][5])==Path(r['copied_source']);method=r['source_identification'];counts[method]+=1
 if method=='127_source_plan':assert Path(plan127[n]['source'])==Path(r['listed_source']) and plan127[n]['sha256']==r['source_sha256']
 elif method=='inferred_sibling_of_65_snapshot':
  row=plan65[n];assert Path(row['source_snapshot'])==Path(r['listed_source']) and Path(r['workspace_candidate'])==Path(row['source_snapshot']).parents[2]/(n.split('.')[-1]+'.lean') and row['source_sha256']==r['source_sha256'];assert sha(row['receipt'])==row['receipt_sha256'] and row['receipt']==r['historical_receipt']
 else:assert method=='recorded_stage_source' and Path(s['source'])==Path(r['listed_source'])
 declared=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',Path(r['copied_source']).read_text(),re.M);assert declared==r['imports']==[x for x in headers[n] if x!='Init']
 for ext in ('stdout','stderr'):assert sha(r['logs'][ext])==s[ext+'_sha256']
 indexed=str(Path(r['workspace_candidate']).relative_to(gitroot)) in tracked;assert indexed==r['workspace_indexed']
 if not indexed:untracked.append(n);alt=Path(r['tracked_byte_identical_alternative']);assert sha(alt)==r['source_sha256'] and str(alt.relative_to(gitroot)) in tracked
 before=s.get('direct_before') or s.get('direct_imports');after=s.get('direct_after') or s.get('direct_imports_after');assert (before is not None)==r['producer_direct_bundles_recorded']
 if before is not None:
  assert before==after
  for dep,b in before.items():
   sel=final['selected_project'].get(dep) or final['selected_outside'].get(dep);assert sel is not None and hs(b)==hs(sel),(n,dep);direct+=1
assert counts=={'127_source_plan':67,'recorded_stage_source':60,'inferred_sibling_of_65_snapshot':59} and sorted(untracked)==['DirectBFSOriginBlockResidue','OffsetBound'] and direct==470
print('PASS 186 reverse-reachable; 294 edges, 141 project/4 outside inputs; producer/source/log, 67+60+59 paths, 184 index/2 alternatives, 470 direct-bundle comparisons and captured topological order independently checked')
import ast
parsed=ast.parse(inv.read_text());assignment=next(x for x in parsed.body if isinstance(x,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='INPUTS' for t in x.targets));pins=ast.literal_eval(assignment.value)
assert len(pins)==9
for rel,digest in pins.items():assert sha(D/rel)==digest
for i in (1,2):
 q=obs.parent/('attempt%02d'%i);receipt=load(q/'terminal.json');assert sha(q/'source.txt')==receipt['checker_sha256'] and sha(q/'stdout')==receipt['stdout_sha256'] and sha(q/'stderr')==receipt['stderr_sha256'];assert receipt['exit']==0
first=load(obs.parent/'attempt01/stdout');assert first['summary']['workspace_indexed']==0
second=load(obs.parent/'attempt02/stdout');assert second['summary']['workspace_indexed']==184
print('PASS nine pinned input receipts and preserved invalid Git-classification attempt01')
