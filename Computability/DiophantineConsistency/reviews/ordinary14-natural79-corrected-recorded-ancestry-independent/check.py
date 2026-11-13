#!/usr/bin/env python3
"""Independent recorded-graph BFS plus replay of prior guard audit. No Lean."""
from pathlib import Path
from collections import deque
import hashlib,json,os,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];R=D/'research';P=Path('/tmp/p72-current-base-extension-attempt02-20261105');B=Path('/tmp/current14-standard-fresh-build-20261104')
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def pin(p,h):
 assert sha(p)==h,(str(p),sha(p));return json.loads(p.read_bytes())
obs=pin(R/'ordinary14-natural79-corrected-recorded-ancestry-audit/observation.json','a3b5167eb6a64bcda2f7f55509ea6741752088bcc029750d8ea2697d4bc542aa')
plan=pin(R/'ordinary14-natural79-corrected-ordered-provider-plan/plan.json','deb0854620b8fb85461df791c545f43c09814b566ec4685517efa1696d46b035')
cut=pin(R/'ordinary14-natural80-qualified-provider-cut/observation.json','c88630304b866b29fe68a11f14f44af210fcd8ea5eed173523ae687c8c157979')
progress=pin(P/'progress.json','f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a')
base=pin(B/'state.json','f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014')
prev=D/'reviews/ordinary14-natural80-recorded-ancestry-independent'; assert sha(prev/'check.py')=='bb7608e2334499f797acdb3b2b64760e72d289d4d3e89b3272e1e55699110c54';assert sha(prev/'result.json')=='59ca10a453b245046bf971c74cf2a588e98ae0a6fd89a58df4c8f4b0f4e429e3'
# The pinned independent natural80 checker itself replays the reviewed root74
# complete bounded source, object, edge and guard audit. No Lean is called.
child=subprocess.run([sys.executable,'-I','-S','-B',str(prev/'check.py')],capture_output=True,check=True);assert child.stdout==(prev/'result.json').read_bytes()
legacy=json.loads(child.stdout)
files=sorted((P/'rows').glob('[0-9][0-9][0-9][0-9].json'));assert len(files)==progress['total']==progress['completed']==681 and sha(files[-1])==progress['last_row_sha256']
rows={}
for f in files:
 r=json.loads(f.read_bytes());assert r['status']=='PASS' and f.name==f"{r['index']:04d}.json" and r['module'] not in rows
 rows[r['module']]=r
records={r['module']:r for r in base['records']};assert len(records)==len(base['records'])==1000 and not set(rows)&set(records)
old=set(cut['selected_project_frontier']);new=set(plan['selected_project_frontier_sources_and_objects']);extra='DiophantineConsistency.Compact44.ReducedNormSigned'
assert len(old)==40 and len(new)==41 and new-old=={extra} and not old-new
for n in sorted(new):
 rec=plan['selected_project_frontier_sources_and_objects'][n]
 for typ in ('source','object'):
  x=rec[typ];p=Path(x['path']);assert p.is_file() and str(p.resolve(strict=True))==x['realpath'] and p.is_symlink()==x['symlink'] and sha(p)==x['sha256']
 producer=rows.get(n,records.get(n));assert producer and rec['source']['sha256']==producer['source_sha256'] and rec['object']['sha256']==producer['object_sha256']
def bfs(seeds):
 q=deque(sorted(seeds));seen=set();external=set();count=0
 while q:
  n=q.popleft()
  if n in seen:continue
  seen.add(n)
  if n in rows: deps=rows[n]['dependencies'];p72=True
  else: assert n in records;deps=records[n]['direct_inputs'];p72=False
  for child,edge in deps.items():
   internal=(child in rows or child in records) if p72 else edge['kind']=='project'
   if internal:assert child in rows or child in records;q.append(child)
   else:external.add(child)
   count+=1
 return seen,external,count
a,ae,ac=bfs(old);b,be,bc=bfs(new)
assert a==b and ae==be and ac==bc and extra in a
assert len(b&set(rows))==627 and len(b&set(records))==919 and bc==4414 and len(be)==80
assert legacy['p72_producers']==627 and legacy['base_producers']==919 and legacy['recorded_edges']==bc and legacy['external_leaf_names']==80
listhash=lambda x:hashlib.sha256(json.dumps(sorted(x),separators=(',',':')).encode()).hexdigest()
assert obs['reached_modules_sha256']==listhash(b) and obs['external_leaves_sha256']==listhash(be)
assert obs['seeds']==41 and obs['natural80_recorded_project_closure_identical'] and obs['added_seeds_vs_natural80']==[extra] and not obs['omitted_seeds_vs_natural80'] and not obs['additional_recorded_project_ancestors']
row=rows[extra];rf=P/'rows/0069.json';res=obs['new_seed_recorded_p72_row'];assert row['index']==res['index']==69 and sha(rf)==res['row_sha256'] and row['source_sha256']==res['source_sha256'] and row['object_sha256']==res['object_sha256'] and row['dependencies']==res['recorded_direct_dependencies'] and len(row['dependencies'])==2 and len(row['direct_guard'])==res['recorded_direct_guard_slots']==60
for path,expected in row['direct_guard'].items():
 p=Path(path);actual=({'realpath':str(p.resolve(strict=True)),'sha256':sha(p)} if os.path.lexists(p) else None)
 assert actual==expected,(path,actual,expected)
assert obs['distinct_guard_slots_checked']==legacy['recorded_guard_slots']==29860 and obs['guard_slots_present']==1751 and obs['guard_slots_absent']==28109 and obs['mismatches']==[]
print(json.dumps({'scope':'separate 40/41 BFS, seed and row69 checks; replay prior full bounded source/edge/guard review; no Lean or producer authentication','old_seeds':len(old),'new_seeds':len(new),'extra_seed_already_reached':True,'p72_producers':627,'base_producers':919,'recorded_edges':bc,'external_leaf_names':len(be),'seed_files_rechecked':len(new)*2,'row69_guards_rechecked':60,'prior_guard_slots_replayed':29860},indent=2,sort_keys=True))
