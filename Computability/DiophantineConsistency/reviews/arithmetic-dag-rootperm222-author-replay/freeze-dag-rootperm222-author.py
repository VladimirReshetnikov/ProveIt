from pathlib import Path
import hashlib,json,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'; REV=D/'reviews'
E=REV/'arithmetic-dag-rootperm222-author-replay'
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def require(b,s):
 if not b:raise RuntimeError(s)
require(not E.exists(),'fresh evidence directory')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
attempts=json.loads(Path('/tmp/dag-rootperm222-controller-author-attempts.json').read_text())
require(len(attempts)==2,'two retained attempts')
observations=[]; states=[]; copied=[]
def verify(r,actual=None,note=None):
 a=rec(actual or r['path']);require(a['sha256']==r['sha256'],'pin '+r['path'])
 observations.append(dict(expected=r,actual=a,**({'note':note}if note else{})))
for i,dirname in enumerate(attempts,1):
 p=Path(dirname);s=json.loads((p/'AUTHOR.json').read_text());states.append(s)
 require(s['status']==('PASS'if i==2 else'FAILED'),'attempt status')
 verify(s['inputs']);inp=json.loads((p/'inputs.json').read_text())
 require(s['counts']==dict(custom=149,Foundation=95,artifacts=434,external=39,boundary_companion_observations=117,refresh=0),'scope')
 for r in inp['pins']:
  if r['path']==s['driver']['path']:
   verify(r,p/'driver.py','Preserved executed driver for this exact attempt; both attempts use the same driver bytes.')
  else:verify(r)
 for provider in inp['actual_providers']:
  verify(provider['actual']);verify(provider['expected'])
 for row in s['records']:
  verify(row['snapshot']);verify(row['log']);verify(row['timing'])
  require(row['snapshot']['sha256']==row['source']['sha256'],'source snapshot')
  require(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'caps')
  if 'object'in row:
   verify(row['object']);require(not Path(row['object']['path']).is_symlink(),'regular fresh target')
  if i==2:verify(row['source'])
 require((p/'driver.py').read_bytes()==Path(s['driver']['path']).read_bytes()if i==2 else True,'final driver')
E.mkdir()
for i,dirname in enumerate(attempts,1):
 p=Path(dirname);dest=E/f'attempt-{i}';dest.mkdir()
 for f in sorted(p.iterdir()):
  if f.is_file()and not f.is_symlink():
   target=dest/f.name;shutil.copyfile(f,target);copied.append(dict(original=rec(f),saved=rec(target)))
for p in [__file__]:
 target=E/Path(p).name;shutil.copyfile(p,target);copied.append(dict(original=rec(p),saved=rec(target)))
guides=[]
for name in ['Dag219Bisim','ArithmeticL2Control254','L2AxiomsPerm','L2RootPerm','ArithmeticDagMacrosPerm222']:
 guides.append(rec(R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'/f'{name}.lean'))
save(E/'freeze-authentication.json',dict(observations=observations,count=len(observations),unique_actual_paths=len({r['actual']['path']for r in observations}),copies=copied,source_only_guides=guides))
files=[]
for p in sorted(E.rglob('*')):
 if p.is_file():files.append(dict(rec(p),path=str(p.relative_to(R))))
save(E/'FILES.json',files)
final=states[-1]
packet=dict(status='PASS',author='controller_certificate',scope='Actual internal equality123, complete AX macro-word and symbolic effect, dispatch141, and unconditional root0 execution with scheduler progress. No full EnumRun/control/tape or source/HA endpoint.',
 final=final,attempts=[dict(state=s,durable=rec(E/f'attempt-{i}'/'AUTHOR.json'))for i,s in enumerate(states,1)],
 inputs=rec(E/'attempt-2'/'inputs.json'),evidence_manifest=rec(E/'FILES.json'),freeze_authentication=rec(E/'freeze-authentication.json'),
 source_only_guides=guides,counts=final['counts'],failed_attempts=1,refresh=0)
out=REV/'arithmetic-dag-rootperm222-replay.json';save(out,packet)
print(json.dumps(dict(packet=rec(out),manifest=rec(E/'FILES.json'),files=len(files),observations=len(observations),sources=[r['source']for r in final['records']],objects=[r['object']for r in final['records']]),indent=2))
