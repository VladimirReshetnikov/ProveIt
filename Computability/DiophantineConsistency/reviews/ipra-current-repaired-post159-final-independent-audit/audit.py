from pathlib import Path
from collections import defaultdict,deque
import hashlib,json,re,graphlib,os,subprocess
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews';D=V/'ipra-current-repaired-post159-final-source-survey';B=V/'ipra-current-repaired-post172-source-survey';PLAN=V/'ipra-frozen-repair-plan-v2/manifest.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
cur=json.loads((D/'manifest.json').read_text());base=json.loads((B/'manifest.json').read_text());plan=json.loads(PLAN.read_text());S=cur['sources'];assert cur['status']=='CANDIDATE_SOURCE_SNAPSHOT' and len(S)==len(base['sources'])==1099
actual={n for n in S if S[n]!=base['sources'][n]};assert actual==set(cur['seeds']) and len(actual)==4
missing=[];bad=[];drift=[];badimports=[];unknown=[]
for n,row in S.items():
 p=D/'sources'/(n.replace('.','/')+'.lean');w=R/row['path']
 if not p.is_file() or p.is_symlink():missing.append(n);continue
 if H(p)!=row['sha256']:bad.append(n)
 if not w.is_file() or H(w)!=row['sha256']:drift.append(n)
 imp=re.findall(r'^import\s+([A-Z][\w.]*)',p.read_text(),re.M)
 if imp!=row['imports']:badimports.append(n)
 unknown += [(n,i) for i in imp if i not in S and i not in cur['external']]
assert not missing and not bad and not badimports and not unknown,(missing,bad,badimports,unknown)
reach=set();stack=[cur['target']]
while stack:
 n=stack.pop()
 if n not in reach:reach.add(n);stack += [i for i in S[n]['imports'] if i in S]
assert reach==set(S)
rev=defaultdict(set)
for n,row in S.items():
 for i in row['imports']:rev[i].add(n)
for r in plan['origin_nodes'].values():
 for dep in r['project_environment']:rev[dep].add(r['module'])
for path in ['/tmp/ipra-current-repaired-build-y6kamkla/state.json','/tmp/ipra-six-drift-replay-42b7hj5k/state.json','/tmp/ipra-eleven-drift-replay-sfz0zyj0/state.json','/tmp/ipra-post172-replay-81f0339y/state.json']:
 state=json.loads(Path(path).read_text());assert state['status']=='PASS'
 for row in state['records']:
  for dep in row['direct_imports']:rev[dep].add(row['name'])
affected=set(actual);q=deque(actual)
while q:
 for n in rev[q.popleft()]-affected:affected.add(n);q.append(n)
assert affected==set(cur['order']) and len(affected)==120
positions={n:i for i,n in enumerate(cur['order'])}
for n in affected:
 for dep in S[n]['imports']:
  if dep in affected:assert positions[dep]<positions[n],(n,dep)
assert cur['order'][-1]==cur['target']
for path,h in cur['input_sha256'].items():assert H(path)==h,path
r=json.loads((D/'lean-deps-receipt.json').read_text());assert r['status']=='PASS_HEADER_DEPS' and set(r['rows'])==actual
for n,row in r['rows'].items():assert hashlib.sha256(row['stdout'].encode()).hexdigest()==row['stdout_sha256'] and row['count']==len(set(S[n]['imports'])-{'Init'})
bad_edges=[];edge_count=0
for node in plan['origin_nodes'].values():
 for dep in node['project_environment']:
  if node['module'] in positions and dep in positions:
   edge_count+=1
   if positions[dep]>=positions[node['module']]:bad_edges.append((node['module'],dep))
for path in ['/tmp/ipra-current-repaired-build-y6kamkla/state.json','/tmp/ipra-six-drift-replay-42b7hj5k/state.json','/tmp/ipra-eleven-drift-replay-sfz0zyj0/state.json','/tmp/ipra-post172-replay-81f0339y/state.json']:
 state=json.loads(Path(path).read_text())
 for row in state['records']:
  for dep in row['direct_imports']:
   if row['name'] in positions and dep in positions:
    edge_count+=1
    if positions[dep]>=positions[row['name']]:bad_edges.append((row['name'],dep))
assert not bad_edges and edge_count==3564
lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');env=dict(os.environ,LEAN_PATH='/tmp/ipra-post172-replay-81f0339y/lib:/tmp/pra14-full-transitive-2x6o__to/package-lib');env.pop('LEAN_SRC_PATH',None)
for n in sorted(actual):
 p=subprocess.run([str(lean),'--deps',str(D/'sources'/(n.replace('.','/')+'.lean'))],env=env,capture_output=True,text=True)
 assert p.returncode==0 and not p.stderr and p.stdout==r['rows'][n]['stdout'],n
late=[n for n,row in S.items() if not (R/row['path']).is_file() or H(R/row['path'])!=row['sha256']]
assert len(late)==len(set(late))
print(json.dumps({'status':'PASS_INDEPENDENT_SOURCE_AUDIT','manifest_sha256':H(D/'manifest.json'),'script_sha256':H(__file__),'sources':len(S),'reachable':len(reach),'changed_seeds':sorted(actual),'affected':len(affected),'retained_environment_edges_checked':edge_count,'live_deps_matched':len(actual),'workspace_drift_before':drift,'workspace_drift_after':late,'scope':'Read-only source graph, snapshot hashes and header resolution; no authentication of project objects, dynamic imports or successor proof.'},indent=2,sort_keys=True))
