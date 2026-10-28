from pathlib import Path
import hashlib,json,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews';B=V/'validator-seed-source-basis222-root-auth'
if B.exists():raise RuntimeError('fresh evidence only')
B.mkdir();observations=[]
def need(x,m):
 if not x:raise RuntimeError(m)
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def check(p,h,size=None):
 a=rec(p);need(a['sha256']==h,'hash '+str(p))
 if size is not None:need(a['bytes']==size,'bytes '+str(p))
 observations.append(a);return a
def pin(x):return check(x['path'],x['sha256'],x.get('bytes'))
def load(p):return json.loads(Path(p).read_text())
def save(p,o):Path(p).write_text(json.dumps(o,indent=2)+'\n')
inputs={'validator-seed-source-basis222-author.md':'5975e48c555ea092adee7cad4c0b53d404887ac300ae395de2b3abfd78ccf13e','validator-seed-source-basis222-peer.md':'82a0c17266176139f61b906fd4e5aff4acff503477a04b84b43b87ea24b31a66','validator-seed-source-basis222-replay.json':'c19fcc42ee10f3c48c1d0cc6fed1fb2838ad08538820466516a6c6b37a0c78fa','validator-seed-source-basis222-peer-replay.json':'8c8a7e204441851eec363f8c1b93b7514bd8a889a771187be0c13c2010578a2f','validator-seed-source-basis222-author-replay/FILES.json':'9bbeadf8153e6033bb9d1aae5a0e4def79c08c7c9a12742e057e7a9d0f264f55','validator-seed-source-basis222-peer-replay/FILES.json':'5073d902e2944ffdf03efc301d6d34d53d6c3b70299d9c5421ebe8233e214881'}
for name,h in inputs.items():check(V/name,h)
a=load(V/'validator-seed-source-basis222-replay.json');p=load(V/'validator-seed-source-basis222-peer-replay.json')
need(a['status']==p['status']==p['state']['status']=='PASS','PASS states')
byhash={}
for name,count in [('validator-seed-source-basis222-author-replay',117),('validator-seed-source-basis222-peer-replay',13)]:
 folder=V/name;manifest=load(folder/'FILES.json');need(len(manifest)==count,'evidence count')
 for x in manifest:
  q=Path(x['path']);need(not q.is_absolute() and '..' not in q.parts,'bundle-relative path')
  actual=check(folder/q,x['sha256'],x.get('bytes'));byhash.setdefault(x['sha256'],[]).append(actual)
cache=V/'validator-seed-source-basis222-cache.json';check(cache,a['input_inventory_sha256']);d=load(cache);need(d==a['inputs'],'author inventory identity')
need(d['counts']==dict(cached_modules=200,foundation=136,artifacts=608,external_boundaries=45),'scope')
for name in ['compiler','manifest','toolchain']:check(d[name],d[name+'_sha256'])
for x in d['parent_receipts']+d['inherited_observations']:pin(x)
for row in d['modules']:
 check(row['source'],row['source_sha256'])
 for ob in row['objects']:pin(ob)
for row in d['external']:pin(row)
need(len(a['attempts'])==12,'all twelve author attempts')
for t in a['attempts']:
 folder=V/'validator-seed-source-basis222-author-replay/attempts'/Path(t['path']).name
 check(folder/'state.json',t['state_sha256']);state=load(folder/'state.json');need(state['status']==t['status'],'historical status')
 for row in state['completed']:
  check(folder/Path(row['snapshot']).name,row['source_sha256'])
  check(folder/Path(row['log']).name,row['log_sha256']);check(folder/Path(row['timing']).name,row['timing_sha256'])
  need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'historical caps')
  if 'object'in row:
   ob=row['object']
   if ob['sha256'] not in byhash:pin(ob)
for k in ['durable_state','inputs','manifest']:pin(p[k])
ps=load(p['durable_state']['path']);need(ps==p['state'],'peer durable state identity');pi=load(p['inputs']['path'])
for x in pi['pins']:pin(x)
for q in pi['providers']:pin(q['first'])
need(len(pi['providers'])==245,'peer primary providers')
reports=0
for ar,pr in zip(a['completed'],p['state']['records'],strict=True):
 need(ar['module']==pr['module'] and ar['exit_code']==pr['exit_code']==0,'leaf identity')
 for k in ['source','snapshot','log','timing']:
  check(ar[k],ar[k+'_sha256']);pin(pr[k])
 for k in ['source','snapshot','log']:need(ar[k+'_sha256']==pr[k]['sha256'],'byte equality '+k)
 pin(ar['object']);pin(pr['object']);need(ar['object']['sha256']==pr['object']['sha256'],'object equality')
 need(ar['axiom_reports']==pr['axiom_reports'],'complete report equality')
 text=Path(pr['log']['path']).read_text();need(not re.search(r'\b(warning|error|sorryAx)\b',text),'diagnostics')
 actual=[list(x) for x in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text)]
 need(actual==pr['axiom_reports'],'actual full reports')
 for _,ax in actual:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'axioms')
 reports+=len(actual)
need(reports==17,'seventeen reports')
providers=[]
for row in d['modules']+d['external']:
 obs=row['objects'] if 'objects'in row else [row]
 for ob in obs:
  relative=Path(*row['module'].split('.')[:-1])/Path(ob['path']).name
  first=next((Path(x)/relative for x in pi['LEAN_PATH'] if(Path(x)/relative).is_file()),None)
  need(first is not None and first.resolve()==Path(ob['path']).resolve(),'actual artifact provider '+row['module'])
  actual=check(first,ob['sha256']);providers.append(dict(module=row['module'],actual=actual,expected=ob))
need(len(providers)==653,'all cached/boundary artifacts')
state=dict(status='PASS',scope='ROOT full final-source and peer-driver review, both frozen packets/attempts/provider reauthentication; no third compiler',counts=d['counts'],observations=len(observations),distinct_paths=len({x['path'] for x in observations}),artifact_providers=len(providers),reports=reports,records=p['state']['records'],provider=p['private']+'/lib',compiler_invocations=0)
save(B/'state.json',state);save(B/'observations.json',observations);save(B/'providers.json',providers);shutil.copyfile(__file__,B/'driver.py')
manifest=[dict(rec(q),path=str(q.relative_to(R))) for q in sorted(B.iterdir()) if q.name!='FILES.json'];save(B/'FILES.json',manifest)
print(json.dumps({k:x for k,x in state.items() if k!='records'},indent=2));print('manifest',rec(B/'FILES.json'))
