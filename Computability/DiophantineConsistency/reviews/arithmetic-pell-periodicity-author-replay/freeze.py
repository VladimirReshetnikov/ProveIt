from pathlib import Path
import hashlib,json,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';V=D/'reviews'
B=V/'arithmetic-pell-periodicity-author-replay'
if B.exists():raise RuntimeError('fresh durable evidence required')
B.mkdir()
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,o):Path(p).write_text(json.dumps(o,indent=2)+'\n')
obs=[]
def check(r):
 a=rec(r['path'])
 if a['sha256']!=r['sha256']:raise RuntimeError('hash '+r['path'])
 obs.append(a)
def nested(o):
 if isinstance(o,dict):
  if 'path' in o and 'sha256' in o:yield o
  for v in o.values():yield from nested(v)
 elif isinstance(o,list):
  for v in o:yield from nested(v)
attempts=[Path(x) for x in Path('/tmp/arithmetic-pell-periodicity-author-attempts').read_text().splitlines()]
plan=json.loads((D/'research/arithmetic-pell-periodicity-cache-plan.json').read_text())
for p in plan['pins']:check(p)
for p in nested(plan['modules']+plan['external']):check(p)
records=[]
for i,p in enumerate(attempts,1):
 out=B/f'attempt-{i}';out.mkdir()
 for src in p.rglob('*'):
  if src.is_file() and 'lib' not in src.relative_to(p).parts:
   target=out/src.relative_to(p);target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,target)
 state=json.loads((p/'state.json').read_text());records.append(dict(private=str(p),state=rec(out/'state.json'),status=state['status']))
 for x in nested(state):
  historical=next((r for r in state['records'] if r['source']['path']==x['path'] and r['source']['sha256']==x['sha256']),None)
  if historical and i<len(attempts):
   if historical['snapshot']['sha256']!=x['sha256']:raise RuntimeError('historical source snapshot')
   check(historical['snapshot'])
  else:check(x)
 for x in nested(json.loads((p/'providers.json').read_text())):check(x)
 console=Path(f'/tmp/arithmetic-pell-periodicity-author-console{i}.log')
 shutil.copyfile(console,out/'console.log')
final=json.loads((attempts[-1]/'state.json').read_text())
if final['status']!='PASS':raise RuntimeError('last must PASS')
if len(attempts)!=2 or records[0]['status']!='FAILED':raise RuntimeError('exact attempt history')
if len(final['records'])!=2 or sum(len(x['axiom_reports']) for x in final['records'])!=10:raise RuntimeError('pair/reports')
shutil.copyfile(__file__,B/'freeze.py')
save(B/'authentication.json',dict(observations=len(obs),distinct_paths=len({x['path'] for x in obs}),pins=obs))
packet=dict(status='PASS',scope='Author two-leaf internal Pell reflection/periodicity proof; no dependency builds or full equation/HA theorem',counts=plan['counts'],attempts=records,records=final['records'],final_private=final['private'],plan=rec(D/'research/arithmetic-pell-periodicity-cache-plan.json'),proposal=rec(D/'research/arithmetic-pell-periodicity-plan.md'),inputs=rec(B/'attempt-2/inputs.json'),providers=rec(B/'attempt-2/providers.json'),authentication=rec(B/'authentication.json'),compiler=plan['compiler'],LEAN_PATH=json.loads((attempts[-1]/'inputs.json').read_text())['LEAN_PATH'])
save(V/'arithmetic-pell-periodicity-replay.json',packet)
manifest=[dict(rec(p),path=str(p.relative_to(R))) for p in sorted(B.rglob('*')) if p.is_file() and p.name!='FILES.json']
save(B/'FILES.json',manifest)
print(json.dumps(dict(packet=rec(V/'arithmetic-pell-periodicity-replay.json'),manifest=rec(B/'FILES.json'),files=len(manifest),observations=len(obs),distinct=len({x['path'] for x in obs}),records=[dict(module=x['module'],seconds=x['seconds'],source=x['source']['sha256'],object=x['object']['sha256']) for x in final['records']]),indent=2))
