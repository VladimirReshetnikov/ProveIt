from pathlib import Path
import hashlib,json,shutil,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';REV=D/'reviews';E=REV/'arithmetic-dag-runtimeperm222-author-replay'
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def need(b,s):
 if not b:raise RuntimeError(s)
need(not E.exists(),'fresh evidence directory');need(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
attempts=json.loads(Path('/tmp/dag-runtimeperm222-controller-author-attempts.json').read_text());need(len(attempts)==4,'four retained attempts')
obs=[];states=[];copies=[];pins={}
def verify(r,p=None,note=None):
 a=rec(p or r['path']);need(a['sha256']==r['sha256'],'pin '+r['path']);pins[a['path']]=a
 obs.append(dict(expected=r,actual=a,**({'note':note}if note else{})))
for i,dirname in enumerate(attempts,1):
 p=Path(dirname);s=json.loads((p/'AUTHOR.json').read_text());states.append(s)
 need(s['status']==('PASS'if i==len(attempts)else'FAILED'),'attempt status')
 verify(s['inputs']);inp=json.loads((p/'inputs.json').read_text())
 need(s['counts']==dict(closure_custom=152,cached_custom=151,Foundation=95,cached_artifacts=436,external=39,boundary_companion_observations=117,proposed_refresh=1,new_leaves=2),'scope')
 for r in inp['pins']:
  if r['path']==s['driver']['path']:verify(r,p/'driver.py','Exact executed driver preserved for this attempt.')
  else:verify(r)
 need(len(inp['actual_providers'])==592,'complete first providers')
 for row in inp['actual_providers']:verify(row['actual']);verify(row['expected'])
 need(len(inp['sources'])==3,'all three inputs captured before compiler')
 for row in inp['sources']:
  verify(row['snapshot']);need(row['snapshot']['sha256']==row['sha256'],'all-input snapshot')
 for row in s['records']:
  verify(row['snapshot']);verify(row['log']);verify(row['timing'])
  need(row['snapshot']['sha256']==row['source']['sha256'],'executed source snapshot')
  need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'caps')
  if 'object'in row:
   verify(row['object']);need(not Path(row['object']['path']).is_symlink(),'fresh output regular')
  if i==len(attempts):verify(row['source'])
 need(s['records'][0]['source']['sha256']=='ec9c249013345061fb2dd99b1cb387f10dfd5d69447100465ff2b7558e949290','unchanged generic source')
 need(s['records'][0]['exit_code']==0,'generic refresh passes')
need(len({s['records'][0]['object']['sha256']for s in states})==1,'generic object identical across attempts')
final=states[-1];need(len(final['records'])==3,'three final commands')
need([len(x['axiom_reports'])for x in final['records']]==[0,0,11],'final reports')
need(final['records'][0]['log']['bytes']==0 and final['records'][1]['log']['bytes']==0,'empty successful main logs')
for r in final['records']:
 need(r['exit_code']==0,'successful command')
 for _,ax in r['axiom_reports']:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))=={'propext','Classical.choice','Quot.sound'},'standard3')
for x in list(pins.values()):verify(x)
E.mkdir()
for i,dirname in enumerate(attempts,1):
 p=Path(dirname);target=E/f'attempt-{i}';target.mkdir()
 for f in sorted(p.iterdir()):
  if f.is_file()and not f.is_symlink():
   dest=target/f.name;shutil.copyfile(f,dest);need(rec(f)['sha256']==rec(dest)['sha256'],'copy');copies.append(dict(original=rec(f),saved=rec(dest)))
shutil.copyfile(__file__,E/Path(__file__).name)
save(E/'freeze-authentication.json',dict(observations=obs,count=len(obs),unique_actual_paths=len(pins),copies=copies,generic_object_identical_across_attempts=True))
files=[dict(rec(p),path=str(p.relative_to(R)))for p in sorted(E.rglob('*'))if p.is_file()];save(E/'FILES.json',files)
guides=[rec(R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'/(n+'.lean'))for n in ['ArithmeticPositiveSimulation254','ArithmeticL2Endpoint254','ArithmeticDagRootPerm222','ArithmeticDagControlPerm222','ArithmeticControlFile']]
packet=dict(status='PASS',author='controller_certificate',scope='Actual internal EnumRunPerm222 and whole DagPerm control halting correspondence for arbitrary scheduler boundaries, exact seed0/4/0, concrete positive clocks, fixed Sigma1 relation and IΣ1 generic clock induction. No p215 tape/boot, source-ZFC or closed PA/HA endpoint.',final=final,attempts=[dict(state=s,durable=rec(E/f'attempt-{i}'/'AUTHOR.json'))for i,s in enumerate(states,1)],inputs=rec(E/'attempt-4'/'inputs.json'),evidence_manifest=rec(E/'FILES.json'),freeze_authentication=rec(E/'freeze-authentication.json'),source_only_guides=guides,counts=final['counts'],failed_attempts=3,refresh=dict(module='BusyBeaver.ZFC.ArithmeticPositiveSimulation254',source=final['records'][0]['source'],object=final['records'][0]['object'],unchanged_source=True,old_historical_object_excluded=True),accepted_provider_supplement=rec(D/'research/c222-dag-runtimeperm222-accepted-provider-20261027.json'),historical_plan=rec(D/'research/c222-dag-runtimeperm222-cache-plan-20261027.json'))
out=REV/'arithmetic-dag-runtimeperm222-replay.json';save(out,packet)
print(json.dumps(dict(packet=rec(out),manifest=rec(E/'FILES.json'),files=len(files),observations=len(obs),unique_paths=len(pins),sources=[r['source']for r in final['records']],objects=[r['object']for r in final['records']]),indent=2))
