#!/usr/bin/env python3
"""Independently compare 31- and 40-seed recorded closures; never invoke Lean."""
from pathlib import Path
from collections import deque
import hashlib,json,subprocess,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=Path('/tmp/p72-current-base-extension-attempt02-20261105');B=Path('/tmp/current14-standard-fresh-build-20261104')
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def pinned(p,h):
 assert sha(p)==h,str(p)
 return json.loads(p.read_bytes())
obs=pinned(D/'research/ordinary14-natural80-recorded-ancestry-audit/observation.json','865b64695a9195dd460f43dbbf1b3ec72cdf50503b0fbbd4de4e4c1c1186d25c')
cut=pinned(D/'research/ordinary14-natural80-qualified-provider-cut/observation.json','c88630304b866b29fe68a11f14f44af210fcd8ea5eed173523ae687c8c157979')
survey=pinned(D/'research/ordinary14-root74-provider-survey/observation.json','14732a54d8f2d3592d31f78d731497a1d804780ca8ec643e3851314868e7b4ab')
progress=pinned(P/'progress.json','f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a')
base=pinned(B/'state.json','f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014')
oldcheck=D/'reviews/ordinary14-root74-recorded-ancestry-independent/check.py'
oldresult=D/'reviews/ordinary14-root74-recorded-ancestry-independent/result.json'
assert sha(oldcheck)=='8468bcb83ebada469468cbd2297214582943f46b971230b03dca2fbde42401d3'
assert sha(oldresult)=='b3011de965960ee93de78beee943da9b878185d29b93948f531ef80bb9b3cd75'
# Replay the existing independently reviewed 31-seed byte/guard audit. This
# executes read-only Python, not Lean, and shares its retained evidence.
child=subprocess.run([sys.executable,'-I','-S','-B',str(oldcheck)],capture_output=True,check=True)
assert child.stdout==oldresult.read_bytes()
legacy=json.loads(child.stdout)
files=sorted((P/'rows').glob('[0-9][0-9][0-9][0-9].json'))
assert len(files)==progress['completed']==progress['total']==681
assert sha(files[-1])==progress['last_row_sha256']
project={}
for file in files:
 row=json.loads(file.read_bytes());assert row['status']=='PASS' and row['module'] not in project
 project[row['module']]=('p72',row)
assert len(base['records'])==1000
for row in base['records']:
 assert row['exit']==0 and row['module'] not in project
 project[row['module']]=('base',row)
old=survey['slim_cut_frontier'];new=sorted(cut['selected_project_frontier'])
assert len(old)==len(set(old))==31 and len(new)==len(set(new))==40 and set(old)<=set(new)
def bfs(seeds):
 queue=deque(seeds);seen=set();external=set();edges=0
 while queue:
  n=queue.popleft()
  if n in seen:continue
  assert n in project,n
  seen.add(n);kind,row=project[n]
  inputs=row['dependencies'] if kind=='p72' else row['direct_inputs']
  for child,edge in inputs.items():
   is_project=(child in project) if kind=='p72' else edge['kind']=='project'
   if is_project:assert child in project;queue.append(child)
   else:external.add(child)
   edges+=1
 return seen,external,edges
oldset,oldexternal,oldedges=bfs(old);newset,newexternal,newedges=bfs(new)
assert oldset==newset and oldexternal==newexternal and oldedges==newedges
assert len(newset & {n for n,(k,_) in project.items() if k=='p72'})==obs['reached_p72_producers']==legacy['reached_p72_producers']==627
assert len(newset & {n for n,(k,_) in project.items() if k=='base'})==obs['reached_base_producers']==legacy['reached_base_producers']==919
assert newedges==obs['recorded_edges']==legacy['recorded_edges']==4414
assert len(newexternal)==obs['external_leaf_names']==legacy['external_leaf_names']==80
for k in ('distinct_guard_slots_checked','guard_slots_present','guard_slots_absent'):
 assert obs[k]==legacy[k],k
assert obs['mismatches']==[] and legacy['mismatches']==0
assert obs['root74_recorded_project_closure_identical'] and obs['added_seeds_vs_root74']==sorted(set(new)-set(old))
def listhash(xs):return hashlib.sha256(json.dumps(sorted(xs),separators=(',',':')).encode()).hexdigest()
assert listhash(newset)==obs['reached_modules_sha256'] and listhash(newexternal)==obs['external_leaves_sha256']
print(json.dumps({'scope':'independent BFS equality and replay of earlier bounded record/hash/guard review; no Lean/provider closure',
 'old_seeds':len(old),'new_seeds':len(new),'additional_seed_names':len(set(new)-set(old)),
 'same_recorded_closure':True,'p72_producers':627,'base_producers':919,'recorded_edges':newedges,
 'external_leaf_names':len(newexternal),'recorded_guard_slots':legacy['distinct_guard_slots_checked']},sort_keys=True,indent=2))
