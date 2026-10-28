from pathlib import Path
import json,hashlib,shutil,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews';B=V/'arithmetic-pell-first-norm-root-auth'
if B.exists():raise RuntimeError('fresh evidence only')
B.mkdir();obs=[]
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def check(x):
 p=Path(x['path']);p=p if p.is_absolute() else R/p;a=rec(p)
 if a['sha256']!=x['sha256']:raise RuntimeError('hash '+str(p))
 if 'bytes' in x and a['bytes']!=x['bytes']:raise RuntimeError('size '+str(p))
 obs.append(a)
def nested(x):
 if isinstance(x,dict):
  if 'path'in x and 'sha256'in x:yield x
  for v in x.values():yield from nested(v)
 elif isinstance(x,list):
  for v in x:yield from nested(v)
def load(p):return json.loads(Path(p).read_text())
def auth(p):
 o=load(p)
 for x in nested(o):check(x)
 return o
pins={'arithmetic-pell-first-norm-author.md':'0682dcbc25c3c3a354ffa1f01eb051f8d1c4dedd2f03a162bb054b126aa77bc7','arithmetic-pell-first-norm-peer.md':'93c04e97863e987577e85f99f357f2c0791b4c7700199fa9997332a3369d033c','arithmetic-pell-first-norm-replay.json':'6021f74a093d33437e5090de9b7f109aa10625ff05307f38c3f63bb4f68122f1','arithmetic-pell-first-norm-peer-replay.json':'56ac5af7354876ddba346e91dc8c1f7d6e028bdd822bd13fb690dd48f288dff6','arithmetic-pell-first-norm-author-replay/FILES.json':'550490a12ec108970af9d45e44bfb73e1c02e1c59a2a567090813cd7faa9c8f5','arithmetic-pell-first-norm-peer-replay/FILES.json':'3f3acf4b1ccf75e7facd4fcbedd6072cdb8571174de37ce1e89796dd8ed89706'}
for p,h in pins.items():check(dict(path=str(V/p),sha256=h))
a=auth(V/'arithmetic-pell-first-norm-replay.json');p=auth(V/'arithmetic-pell-first-norm-peer-replay.json')
if a['status']!=p['status'] or p['status']!='PASS':raise RuntimeError('PASS')
for f,count in [('arithmetic-pell-first-norm-author-replay/FILES.json',29),('arithmetic-pell-first-norm-peer-replay/FILES.json',14)]:
 if len(auth(V/f))!=count:raise RuntimeError('evidence count')
plan=auth(a['plan']['path']);auth(a['inputs']['path']);auth(a['providers']['path']);auth(a['authentication']['path'])
ps=auth(p['state']['path']);pi=auth(p['inputs']['path']);providers=auth(p['providers']['path'])
if ps['status']!='PASS':raise RuntimeError('peer state PASS')
if plan['counts']!=a['counts'] or p['counts']!=a['counts']:raise RuntimeError('counts')
reports=0
for ar,pr in zip(a['records'],p['records'],strict=True):
 for r in [ar,pr]:
  if r['exit_code']!=0:raise RuntimeError('exit')
  for k in ['source','snapshot','object','log','timing']:check(r[k])
 for k in ['source','object','log']:
  if ar[k]['sha256']!=pr[k]['sha256']:raise RuntimeError('byte equality '+k)
 if ar['axiom_reports']!=pr['axiom_reports']:raise RuntimeError('reports equality')
 text=Path(pr['log']['path']).read_text()
 if re.search(r'\b(warning|error|sorryAx)\b',text):raise RuntimeError('diagnostics')
 for _,ax in pr['axiom_reports']:
  if not set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}:raise RuntimeError('axioms')
 reports+=len(pr['axiom_reports'])
if reports!=11:raise RuntimeError('eleven reports')
for row in providers:
 if row['actual']['sha256']!=row['expected']['sha256']:raise RuntimeError('provider identity')
state=dict(status='PASS',scope='ROOT author reauthentication after independent peer source review and fresh pair; no third compile',counts=plan['counts'],observations=len(obs),distinct_paths=len({x['path'] for x in obs}),reports=reports,records=p['records'],provider=p['private']+'/lib',compiler_invocations=0)
for n,o in [('state.json',state),('observations.json',obs)]: (B/n).write_text(json.dumps(o,indent=2)+'\n')
shutil.copyfile(__file__,B/'driver.py')
m=[dict(rec(q),path=str(q.relative_to(R))) for q in sorted(B.iterdir()) if q.name!='FILES.json'];(B/'FILES.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({k:v for k,v in state.items() if k!='records'},indent=2));print('manifest',rec(B/'FILES.json'))
