#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys,tarfile
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-freej88-provider-survey';cache={}
def sha(q):
 q=Path(q)
 if q not in cache:
  with q.open('rb') as f:cache[q]=hashlib.file_digest(f,'sha256').hexdigest()
 return cache[q]
for n,h in {'README.md':'703d50fb71ec3eba734f6c7d39dac89bd575418d6583f5aad8e516c277ed5037','inspect.py':'08fea8f7be3d0ac22e59bcf7265b5b023a2e1ede4a89c0d062c50fdce359e8ab','observation.json':'ff8c85cefd57297ed6fcec7da1a8fbc7f53e777506464e7aed53060f7eeba024'}.items():assert sha(p/n)==h
f=json.loads((p/'observation.json').read_text());r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'inspect.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr;x=json.loads(r.stdout)
assert {k:v for k,v in x.items() if k not in ('tmp_free_bytes','head')}=={k:v for k,v in f.items() if k not in ('tmp_free_bytes','head')}
assert x['status']=='READ_ONLY_OBSERVATION_NOT_BUILD_READINESS' and x['inspector_sha256']==sha(p/'inspect.py') and not x['prior_endpoint_route_issues']
prefix='DiophantineConsistency.Compact44.'; names=[prefix+'FreeJ13','P88PairGraph',prefix+'FreeJ13Halt','P88PairModel','P88PairEndpoint'];assert x['planned_stages']==names and set(x['project_sources'])=={names[0],names[2]}
front={prefix+n for n in ('FreeJSumSquares','FreeJSignedTransport','FreeJGraphAuxiliary','QCube92Halt','IPRAOrdinary12Chain')};assert set(x['p72_frontier'])==front
# Independently check direct source imports and a valid topological order.
sources={n:repo/info['source'] for n,info in x['project_sources'].items()};draft=base/'research/ordinary13-freej88-lean-draft';sources.update({n:draft/(n+'.lean') for n in ('P88PairGraph','P88PairModel','P88PairEndpoint')})
assert len(sources)==5
expected={names[0]:[prefix+'FreeJSumSquares',prefix+'FreeJSignedTransport','Mathlib.Tactic.LinearCombination'],names[1]:[names[0]],names[2]:[names[0],prefix+'FreeJGraphAuxiliary',prefix+'QCube92Halt'],names[3]:[names[1],names[2],prefix+'IPRAOrdinary12Chain'],names[4]:[names[3]]};positions={n:i for i,n in enumerate(names)}
for n,q in sources.items():
 imports=[]
 for line in q.read_text().splitlines():
  m=re.match(r'^\s*import\s+([^\n-]+)',line)
  if m:imports.extend(m[1].split())
 assert imports==expected[n]
 for dep in imports:
  if dep in positions:assert positions[dep]<positions[n]
  else:assert dep in front or dep=='Mathlib.Tactic.LinearCombination'
# Reconstruct the 5-frontier captured producers from the frozen archive and
# base state, verifying objects, source snapshots, logs, edges, and guards.
p72=Path('/tmp/p72-current-base-extension-attempt02-20261105');basep=Path('/tmp/current14-standard-fresh-build-20261104');survey=json.loads((base/'research/p72-current-base-source-survey/result.json').read_text());order=survey['extension_order'];ix={n:i for i,n in enumerate(order)};bs=json.loads((basep/'state.json').read_text());br={r['module']:r for r in bs['records']};manifest=json.loads((base/'research/current14-standard-fresh-rebuild-preflight/snapshot-manifest.json').read_text());snapshot=json.loads((p72/'source-snapshot.json').read_text())
assert bs['status']=='PASS' and len(br)==1000 and len(ix)==681
archive=base/'research/p72-current-base-extension-build-attempt02/terminal/stage-evidence.tar.gz';assert sha(archive)=='884525ff2103d805cdb8b891fedaa9cf8b9be4bc5f1c67efbf8e95353b533541';arch={}
with tarfile.open(archive,'r:gz') as t:
 for m in t:
  if m.isfile() and (m.name.startswith('rows/') or m.name.startswith('src/') or m.name.startswith('logs/')):arch[m.name]=hashlib.sha256(t.extractfile(m).read()).hexdigest()
seenp=set();seenb=set();pq=list(front);bq=[];pe=be=pg=bg=0
def guard(items):
 for s,v in items.items():
  q=Path(s)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
while pq:
 n=pq.pop()
 if n in seenp:continue
 seenp.add(n);i=ix[n];key=f'rows/{i:04d}.json';rowp=p72/key;assert sha(rowp)==arch[key];row=json.loads(rowp.read_text());assert row['module']==n and row['index']==i and row['status']=='PASS' and row['source_sha256']==snapshot[n]
 srcname='src/'+n.replace('.','/')+'.lean';src=p72/srcname;workspace=repo/survey['project_sources'][n]['source'];assert sha(src)==sha(workspace)==arch[srcname]==snapshot[n]
 obj=p72/'lib'/(n.replace('.','/')+'.olean');assert sha(obj)==row['object_sha256']
 for typ,run in zip(('deps','compile'),row['runs']):
  assert run['exit']==0 and run['stop_reason'] is None and not run['monitor_errors'] and not run['observed_descendant_pids'];log=Path(run['log']);assert sha(log)==run['log_sha256']==arch[f'logs/{i:04d}-{typ}.txt']
 assert len(row['runs'])==2;pg+=len(row['direct_guard']);guard(row['direct_guard'])
 for dep,item in row['dependencies'].items():
  q=Path(item['path']);assert q.is_file() and str(q.resolve())==item['realpath'] and sha(q)==item['sha256'];pe+=1
  if dep in ix:pq.append(dep)
  elif dep in br:bq.append(dep)
while bq:
 n=bq.pop()
 if n in seenb:continue
 seenb.add(n);row=br[n];assert row['exit']==0;src=repo/manifest['sources'][n]['workspace_path'];assert sha(src)==row['source_sha256']==manifest['sources'][n]['sha256'];obj=basep/'lib'/(n.replace('.','/')+'.olean');assert sha(obj)==row['object_sha256'];assert sha(Path(row['log']))==row['log_sha256'];bg+=len(bs['outputs'][n]);guard(bs['outputs'][n])
 for dep,item in row['direct_inputs'].items():
  q=Path(item['path']);assert q.is_file() and sha(q)==item['sha256'];be+=1
  if item['kind']=='project':assert dep in br;bq.append(dep)
assert (len(seenp),len(seenb),pe,be,pg,bg)==(616,918,1728,2647,51840,9180)
assert seenp==set(x['recorded_freej_p72_modules']) and seenb==set(x['recorded_freej_base_modules'])
# Independently verify subset of prior six-frontier captured ancestry.
prior=json.loads((base/'research/ordinary13-p73-provider-preflight/observation.json').read_text());assert front <= set(prior['endpoint']['p72_frontier']);P=set();B=set();pq=list(prior['endpoint']['p72_frontier']);bq=[]
while pq:
 n=pq.pop()
 if n in P:continue
 P.add(n);row=json.loads((p72/'rows'/f'{ix[n]:04d}.json').read_text())
 for dep in row['dependencies']:
  if dep in ix:pq.append(dep)
  elif dep in br:bq.append(dep)
while bq:
 n=bq.pop()
 if n in B:continue
 B.add(n)
 for dep,item in br[n]['direct_inputs'].items():
  if item['kind']=='project':bq.append(dep)
assert len(P)==679 and len(B)==918 and seenp<=P and seenb<=B
for n,item in x['p72_frontier_paths'].items():
 q=Path(item['path']);assert q.is_file() and str(q.resolve())==item['realpath'] and sha(q)==item['sha256']==x['p72_frontier'][n]['object_sha256']
init=x['implicit_init_observation'];q=Path(init['path']);assert q.is_file() and str(q.resolve())==init['realpath'] and sha(q)==init['sha256']
assert not x['target_artifacts_in_named_roots'] and not x['p72_snapshot_target_sources'];suffix=x['target_suffixes_checked'];assert len(suffix)==13
for n in names:
 stem=n.replace('.','/');assert not os.path.lexists(p72/'src'/(stem+'.lean'))
 for root in x['target_roots_checked']:
  for ext in suffix:assert not os.path.lexists(Path(root['path'])/(stem+ext))
print(json.dumps({'status':'PASS_READ_ONLY_INDEPENDENT_REVIEW','current_sources':2,'draft_clients':3,'p72_frontier':5,'selected_p72_objects':len(seenp),'selected_base_objects':len(seenb),'direct_edges':pe+be,'guard_slots':pg+bg,'prior_route_subset':True,'frozen_tmp_free_bytes':f['tmp_free_bytes'],'fresh_tmp_free_bytes':x['tmp_free_bytes'],'scope':'Recorded source/routes only; no Lean dependency trace, future-root or complete package/dynamic closure, build readiness or file binding.'},indent=2))
