from pathlib import Path
import hashlib,json,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
O=V/'arithmetic-control215-table-root-auth';O.mkdir(exist_ok=False)
obs=[]
def require(x,m):
 if not x:raise RuntimeError(m)
def record(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def check(r,role):
 p=Path(r['path']);p=p if p.is_absolute() else R/p
 a=record(p);require(a['sha256']==r['sha256'],'hash '+str(p))
 if 'bytes' in r:require(a['bytes']==r['bytes'],'size '+str(p))
 obs.append(dict(a,role=role));return a
def nested(x):
 if isinstance(x,dict):
  if 'path' in x and 'sha256' in x:yield x
  for v in x.values():yield from nested(v)
 elif isinstance(x,list):
  for v in x:yield from nested(v)
def load(p):return json.loads(Path(p).read_text())
def inputs(p,role):
 o=load(p)
 for r in nested(o):check(r,role)
 return o
pins={
'arithmetic-control215-table-author.md':'36d09038ed95bb8f31fbe51e40aca69e8ab90cfe7a64ffcfe1432ce5eb0fae38',
'arithmetic-control215-table-peer.md':'6d4b69c40f447ffbbfe4b02891d957d816cdf3cdc1f8bde2e832bd5927773f80',
'arithmetic-control215-table-replay.json':'7cd8b72d782569b9306553e11e99eb3b62292c0ab5a99ad34d166031a8991609',
'arithmetic-control215-table-peer-replay.json':'6a39c93b890faceff9f1364b43bcc5e431f6ff6e9beb185913eb0797e07ab830',
'arithmetic-control215-table-author-replay/FILES.json':'c9ee0fa5429d51007d5023df4572debd52987ed19466135f7715af8f02e5ce4f',
'arithmetic-control215-table-peer-replay/FILES.json':'86c7afe6d69844564d5e158414972bf3ebc70905a734cf4857f7900756e2cd55'}
for p,h in pins.items():check(dict(path=str(V/p),sha256=h),'frozen input')
a=inputs(V/'arithmetic-control215-table-replay.json','author packet')
p=inputs(V/'arithmetic-control215-table-peer-replay.json','peer packet')
require(a['status']==p['status']=='PASS','packet status')
for name in ['arithmetic-control215-table-author-replay/FILES.json','arithmetic-control215-table-peer-replay/FILES.json']:
 manifest=inputs(V/name,'durable evidence');require(len(manifest)==16,'manifest count')
d=inputs(a['final_inputs']['path'],'author selected inputs')
plan=inputs(a['original_plan']['path'],'historical plan')
inputs(a['authentication']['path'],'author freeze pins')
s=inputs(p['state']['path'],'peer state');require(s['status']=='PASS','peer state')
inputs(V/'arithmetic-control215-table-peer-replay/pins.json','peer pins')
providers=inputs(V/'arithmetic-control215-table-peer-replay/providers.json','peer actual providers')
inputs(a['provider_supplement']['root_state']['path'],'accepted root objects')
m=Path(a['provider_supplement']['root_manifest']['path'])
for r in load(m):
 q=Path(r['path']);q=q if q.is_absolute() else m.parent/q
 if not q.exists():q=R/r['path']
 check(dict(r,path=str(q)),'accepted root evidence')
expected=dict(custom=140,Foundation=95,artifacts=425,external=39,fresh_prerequisites=0)
require(a['counts']==p['counts']==d['counts']==s['counts']==expected,'exact scope')
require(len(d['modules'])==140 and sum(r['module'].startswith('Foundation.') for r in d['modules'])==95,'modules')
require(sum(len(r['objects']) for r in d['modules'])==425 and len(d['external'])==39,'artifacts/boundaries')
reports=0
for ar,pr,sr in zip(a['records'],p['records'],s['records'],strict=True):
 require(ar['module']==pr['module']==sr['module'],'module identity')
 for r in [ar,pr,sr]:
  require(r['exit_code']==0,'exit')
  for k in ['source','snapshot','object','log','timing']:check(r[k],'final result')
 require(ar['source']['sha256']==pr['source']['sha256']==sr['source']['sha256'],'source equality')
 require(ar['object']['sha256']==pr['object']['sha256']==sr['object']['sha256'],'object equality')
 require(ar['log']['sha256']==pr['log']['sha256']==sr['log']['sha256'],'full log equality')
 log=Path(ar['log']['path']).read_text()
 require(not re.search(r'\b(warning|error|sorryAx)\b',log),'diagnostics')
 rs=[list(x) for x in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log)]
 require(rs==ar['axiom_reports']==pr['axiom_reports']==sr['axiom_reports'],'reports identity')
 require(all(set(re.findall(r'[A-Za-z][A-Za-z.]*',x))<={'propext','Classical.choice','Quot.sound'} for _,x in rs),'axioms')
 reports+=len(rs)
require(reports==9,'nine reports')
da=inputs(p['data_audit']['path'],'independent data audit');require(da['status']=='PASS','data audit')
require(da['nodes']==179 and da['leaves']==4751 and da['blocks']==75 and da['last_block_rows']==15,'data coverage')
require(da['physical_map']==[6,2,0,4,3,7,8,5,1] and da['repacked_equal'] and da['all_rows_equal'],'literal data')
source=Path(a['records'][0]['source']['path']).read_text()
hexword=re.findall(r'def packed215 : Nat := 0x([0-9a-f]+)',source)
require(len(hexword)==1 and hashlib.sha256(hexword[0].encode()).hexdigest()==da['hex_sha256'],'full hexadecimal pin')
require(len(hexword[0])==42759 and int(hexword[0],16).bit_length()==171033,'literal size')
require([int(n) for n in re.findall(r'Fin.cases block_(\d+)',source)]==list(range(75)),'all block wiring')
for r in providers:require(r['actual']['sha256']==r['expected']['sha256'],'actual provider equality')
state=dict(status='PASS',scope='ROOT reauthentication after full proof-text and independent replay review; no third compiler invocation',counts=expected,observations=len(obs),distinct_paths=len({r['path'] for r in obs}),reports=reports,records=a['records'],peer_provider=p['private_provider'],data_audit=da,compiler_invocations=0)
(O/'observations.json').write_text(json.dumps(obs,indent=2)+'\n')
(O/'state.json').write_text(json.dumps(state,indent=2)+'\n')
shutil.copyfile(__file__,O/'driver.py')
manifest=[dict(record(q),path=str(q.relative_to(R))) for q in sorted(O.iterdir()) if q.name!='FILES.json']
(O/'FILES.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:v for k,v in state.items() if k not in ['records','data_audit']},indent=2))
print('manifest',record(O/'FILES.json'))
