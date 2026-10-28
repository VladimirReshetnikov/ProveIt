from pathlib import Path
import hashlib,json,shutil,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';REV=D/'reviews';E=REV/'arithmetic-machine-tape215-author-replay'
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def need(b,s):
 if not b:raise RuntimeError(s)
need(not E.exists(),'fresh evidence directory');need(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
attempts=json.loads(Path('/tmp/machine-tape215-controller-author-attempts.json').read_text());need(len(attempts)>=1,'retained attempts')
obs=[];states=[];copies=[];pins={}
def verify(r,p=None,note=None):
 a=rec(p or r['path']);need(a['sha256']==r['sha256'],'pin '+r['path']);pins[a['path']]=a
 obs.append(dict(expected=r,actual=a,**({'note':note}if note else{})))
for i,dirname in enumerate(attempts,1):
 p=Path(dirname);s=json.loads((p/'AUTHOR.json').read_text());states.append(s)
 need(s['status']==('PASS'if i==len(attempts)else'FAILED'),'attempt status')
 verify(s['inputs']);inp=json.loads((p/'inputs.json').read_text())
 need(s['counts']==dict(custom=145,Foundation=95,cached_artifacts=430,boundary=41,boundary_companions=123,refresh=0,proposed_fresh_leaves=2),'scope')
 for r in inp['pins']:
  if r['path']==s['driver']['path']:verify(r,p/'driver.py','Exact executed driver preserved for this attempt.')
  else:verify(r)
 need(len(inp['actual_providers'])==594,'complete first providers')
 for row in inp['actual_providers']:verify(row['actual']);verify(row['expected'])
 need(len(inp['sources'])==2,'both inputs captured before compiler')
 for row in inp['sources']:
  verify(row['snapshot']);need(row['snapshot']['sha256']==row['sha256'],'all-input snapshot')
 for row in s['records']:
  verify(row['snapshot']);verify(row['log']);verify(row['timing'])
  need(row['snapshot']['sha256']==row['source']['sha256'],'executed source snapshot')
  need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'caps')
  if 'object'in row:
   verify(row['object']);need(not Path(row['object']['path']).is_symlink(),'fresh output regular')
  if i==len(attempts):verify(row['source'])
final=states[-1];need(len(final['records'])==2,'two final commands')
need([len(x['axiom_reports'])for x in final['records']]==[0,13],'final reports')
need(final['records'][0]['log']['bytes']==0,'empty successful main log')
for r in final['records']:
 need(r['exit_code']==0,'successful command')
 for _,ax in r['axiom_reports']:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'standard only')
for x in list(pins.values()):verify(x)
E.mkdir()
for i,dirname in enumerate(attempts,1):
 p=Path(dirname);target=E/f'attempt-{i}';target.mkdir()
 for f in sorted(p.iterdir()):
  if f.is_file()and not f.is_symlink():
   dest=target/f.name;shutil.copyfile(f,dest);need(rec(f)['sha256']==rec(dest)['sha256'],'copy');copies.append(dict(original=rec(f),saved=rec(dest)))
shutil.copyfile(__file__,E/Path(__file__).name)
save(E/'freeze-authentication.json',dict(observations=obs,count=len(obs),unique_actual_paths=len(pins),copies=copies))
files=[dict(rec(p),path=str(p.relative_to(R)))for p in sorted(E.rglob('*'))if p.is_file()];save(E/'FILES.json',files)
packet=dict(status='PASS',author='controller_certificate',scope='Actual decimal215 arbitrary internal tape-step relabeling and represented continuation; all13 checked boot chunks give exact95714 prefix through the same Sigma1 run graph. Arbitrary-internal halting iff continuation at the literal boot code. No site executor, scheduler/tape calibration, source validity or HA endpoint.',final=final,attempts=[dict(state=s,durable=rec(E/f'attempt-{i}'/'AUTHOR.json'))for i,s in enumerate(states,1)],inputs=rec(E/f'attempt-{len(attempts)}'/'inputs.json'),evidence_manifest=rec(E/'FILES.json'),freeze_authentication=rec(E/'freeze-authentication.json'),counts=final['counts'],failed_attempts=len(attempts)-1,historical_plan=rec(D/'research/c222-tape215-plan-20261027/cache-plan.json'),data_audit=rec(D/'research/c222-tape215-plan-20261027/boot-state-audit.json'),proposal=rec(D/'research/c222-tape215-proposal-20261027.md'))
out=REV/'arithmetic-machine-tape215-replay.json';save(out,packet)
print(json.dumps(dict(packet=rec(out),manifest=rec(E/'FILES.json'),files=len(files),observations=len(obs),unique_paths=len(pins),sources=[r['source']for r in final['records']],objects=[r['object']for r in final['records']]),indent=2))
