from pathlib import Path
import hashlib,json,os,re,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency';V=D/'reviews'
B=V/'arithmetic-pell-squared-seed-author-replay'
OUT=V/'arithmetic-pell-squared-seed-replay.json'
OBS=[]
def need(ok,message):
 if not ok:raise RuntimeError(message)
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def check(z,actual=None):
 a=rec(actual or z['path']);need(a['sha256']==z['sha256'],'hash '+z['path'])
 if 'bytes'in z:need(a['bytes']==z['bytes'],'size '+z['path'])
 OBS.append(dict(expected=z,actual=a));return a
def read(p):return json.loads(Path(p).read_text())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
need(not B.exists()and not OUT.exists(),'fresh durable evidence')
need(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
runs=read('/tmp/arithmetic-pell-squared-seed-author-runs.json');need(len(runs)==2,'two author attempts')
states=[read(Path(p)/'state.json')for p in runs]
need([s['status']for s in states]==['FAILED','PASS'],'chronology')
attempts=[]
for private,s in zip(runs,states,strict=True):
 p=Path(private);check(s['driver']);check(s['inputs']);inp=read(p/'inputs.json')
 check(inp['profile_reference']);check(inp['scope']);check(inp['providers']);check(inp['authentication']);check(inp['compiler'])
 source_snapshots={z['path']:z['snapshot']for z in inp['sources']}
 for z in inp['sources']:
  check(z,z['snapshot']['path']);check(z['snapshot'])
 for z in read(inp['authentication']['path'])['pins']:
  check(z,source_snapshots[z['path']]['path']if z['path']in source_snapshots else None)
 providers=read(inp['providers']['path']);need(len(providers)==498,'498 providers')
 for z in providers:check(z['expected']);check(z['actual'])
 for row in s['records']:
  need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'caps')
  for key in ['snapshot','log','timing']:check(row[key])
  if 'object'in row:check(row['object'])
 attempts.append(dict(private=private,status=s['status'],state=rec(p/'state.json')))
final=states[-1];P=Path(runs[-1]);need(len(final['records'])==2,'both final leaves')
for row,wanted in zip(final['records'],[0,4],strict=True):
 need(row['exit_code']==0,'successful final command')
 for key in ['source','snapshot','object','log','timing']:check(row[key])
 text=Path(row['log']['path']).read_text();need(not re.search(r'\b(?:warning|error|sorryAx)\b',text),'clean final log')
 reports=[list(z)for z in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)]
 need(reports==row['axiom_reports']and len(reports)==wanted,'all final reports')
 for _,ax in reports:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
 need(not Path(row['object']['path']).is_symlink(),'fresh regular object')
B.mkdir()
for i,private in enumerate(runs,1):
 p=Path(private);target=B/f'attempt-{i}';target.mkdir()
 for source in sorted(p.iterdir()):
  if source.is_file()and not source.is_symlink():os.link(source,target/source.name)
 for source in sorted((p/'logs').iterdir()):
  if source.is_file()and not source.is_symlink():os.link(source,target/source.name)
 attempts[i-1]['durable']=rec(target/'state.json')
shutil.copyfile(__file__,B/'freeze.py')
save(B/'final-authentication.json',dict(observations=OBS,count=len(OBS),
 distinct_paths=len({z['actual']['path']for z in OBS}),scope='Historical working-source pins checked against their exact pre-command snapshots; all cached pins, providers, drivers, logs and outputs reauthenticated.'))
inp=read(P/'inputs.json')
files=[p for p in sorted(B.rglob('*'))if p.is_file()]
files.extend([D/'research/arithmetic-pell-squared-seed-proposal.md',
 D/'Lean/DiophantineConsistency/ArithmeticPellSquaredSeed.lean',D/'Lean/DiophantineConsistency/ArithmeticPellSquaredSeedChecks.lean'])
save(B/'FILES.json',[dict(rec(p),path=str(p.relative_to(R)))for p in files])
packet=dict(status='PASS',author='ROOT',scope='Actual internal strong seed at explicit index R*ycoord(R,a), with positive f/i and the literal additive norm; remaining simultaneous cofinal and auxiliary converse witnesses remain open.',
 counts=inp['counts'],records=final['records'],attempts=attempts,private_provider=str(P/'lib'),
 final_state=rec(P/'state.json'),inputs=rec(P/'inputs.json'),providers=rec(P/'providers.json'),
 authentication=rec(P/'authentication.json'),freeze_authentication=rec(B/'final-authentication.json'),
 plan=inp['profile_reference'],scope_supplement=inp['scope'],compiler=inp['compiler'],LEAN_PATH=inp['LEAN_PATH'],
 driver=rec(P/'driver.py'),manifest=rec(B/'FILES.json'),historical_attempts=2,
 evidence_storage='Regular hardlinks of immutable terminal metadata and source snapshots; all paths/hashes retained and fresh compiled outputs remain separate. Outer packet and author receipt are separately pinned, outside the manifest to avoid cyclic hashes.')
save(OUT,packet)
print(json.dumps(dict(packet=rec(OUT),manifest=rec(B/'FILES.json'),files=len(files),
 observations=len(OBS),distinct_paths=len({z['actual']['path']for z in OBS}),free_bytes=shutil.disk_usage('/tmp').free),indent=2))
