from pathlib import Path
import json,hashlib,shutil,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews';B=V/'arithmetic-pell-periodicity-root-auth'
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
pins={'arithmetic-pell-periodicity-author.md':'acf00e1102c1d99f0554ab0c39f51129358a4c0c0a852243d8ec439957290580','arithmetic-pell-periodicity-peer.md':'c1b88c1f1bb2bd8d8d61835bbf67ecd0dafe942981bd281a1222da3660f71f3d','arithmetic-pell-periodicity-replay.json':'a6a7c5f47e3b36748213b4f3b31e6c6aa18c710a03b1b758f3576be97192ad26','arithmetic-pell-periodicity-peer-replay.json':'5a4a46bb30bdcc70940c4ea683015297610fdcdd8cb9a53f6e03fcfca375f7ea','arithmetic-pell-periodicity-author-replay/FILES.json':'85235f722a77322ad687ff847a130f828cfc68010d5cb7186464f40067b23fa0','arithmetic-pell-periodicity-peer-replay/FILES.json':'c1ce941bcd836eb68bee2e435c2b49564c75dc11285377e1f4159ba4c746cd81'}
for p,h in pins.items():check(dict(path=str(V/p),sha256=h))
a=auth(V/'arithmetic-pell-periodicity-replay.json');p=auth(V/'arithmetic-pell-periodicity-peer-replay.json')
if a['status']!=p['status'] or p['status']!='PASS':raise RuntimeError('PASS')
for f,count in [('arithmetic-pell-periodicity-author-replay/FILES.json',29),('arithmetic-pell-periodicity-peer-replay/FILES.json',14)]:
 if len(auth(V/f))!=count:raise RuntimeError('evidence count')
plan=auth(a['plan']['path']);auth(a['inputs']['path']);auth(a['providers']['path']);auth(a['authentication']['path'])
ps=auth(p['state']['path']);pi=auth(p['inputs']['path']);auth(p['authentication']['path'])
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
if reports!=10:raise RuntimeError('ten reports')
for row in pi['providers']:
 if row['actual']['sha256']!=row['expected']['sha256']:raise RuntimeError('provider identity')
state=dict(status='PASS',scope='ROOT author reauthentication after independent peer source review and fresh pair; no third compile',counts=plan['counts'],observations=len(obs),distinct_paths=len({x['path'] for x in obs}),reports=reports,records=p['records'],provider=p['private_provider'],compiler_invocations=0)
for n,o in [('state.json',state),('observations.json',obs)]: (B/n).write_text(json.dumps(o,indent=2)+'\n')
shutil.copyfile(__file__,B/'driver.py')
m=[dict(rec(q),path=str(q.relative_to(R))) for q in sorted(B.iterdir()) if q.name!='FILES.json'];(B/'FILES.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({k:v for k,v in state.items() if k!='records'},indent=2));print('manifest',rec(B/'FILES.json'))
