from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';parent=Path('/tmp/adaptive13-halfbinomial-postmerge-c0q5x_v3');poprefresh=Path('/tmp/adaptive13-population-refresh-8rcbg45y');winrefresh=Path('/tmp/adaptive13-window-refresh-s_sg2q3z');pell=Path('/tmp/adaptive13-indices-seijhykj')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
names=['ArithmeticHalfBinomialSandwich','ArithmeticHalfBinomial','ArithmeticAdaptivePopulation2011','ArithmeticAdaptivePopulation2011Checks','ArithmeticAdaptiveWindow2011','ArithmeticAdaptiveWindow2011Checks']+[f'ArithmeticAdaptiveConstruction{x}2011{suffix}' for x in ['Transport','Strong','Aux','AuxClient','AuxPhase','Carrier'] for suffix in ['', 'Checks']]
pstate=read(parent/'state.json');assert pstate['status']=='FAILED';assert len(pstate['records'])==17 and all(r['exit']==0 for r in pstate['records']);assert sha(parent/'providers.json')==pstate['providers_sha256']
for item in read(parent/'providers.json'):assert sha(item['path'])==item['sha256']
for r in pstate['records']:
 
 assert sha(S/(r['name']+'.lean'))==r['source_sha256']
 assert sha(parent/'lib/DiophantineConsistency'/(r['name']+'.olean'))==r['object_sha256']
popstate=read(poprefresh/'state.json');assert popstate['status']=='PASS'
for r in popstate['records']:
 if r['name'] not in ['ArithmeticBinomLegendre','ArithmeticHalfBinomial','ArithmeticHalfBinomialSandwich']:assert sha(S/(r['name']+'.lean'))==r['source_sha256']
 assert sha(poprefresh/'lib/DiophantineConsistency'/(r['name']+'.olean'))==r['object_sha256']
roots={'DiophantineConsistency':S,'FirstOrder':R/'Logic/FirstOrder/Lean/FirstOrder','PAHF':R/'Logic/Interpretability/PAHF/Lean/PAHF'}
winstate=read(winrefresh/'state.json');assert winstate['status']=='PASS'
for r in winstate['records']:
 if r['name']!='ArithmeticCarrierRadix2011':assert sha(roots[r['namespace']]/(r['name']+'.lean'))==r['source_sha256']
pellstate=read(pell/'state.json');assert pellstate['status']=='PASS';pr=next(r for r in pellstate['records'] if r['name']=='ArithmeticPellRecurrence');assert sha(S/'ArithmeticPellRecurrence.lean')==pr['source_sha256'];assert sha(parent/'lib/DiophantineConsistency/ArithmeticPellRecurrence.olean')==pr['object_sha256']
p=read('/tmp/arithmetic-signed-pairs-peer-f4gz2l0f/inputs.json');boundary=p['LEAN_PATH'][1:];assert all('/.lake/packages/' in x or '/toolchains/' in x for x in boundary)
assert shutil.disk_usage('/tmp').free>=512*1024**2
w=Path(tempfile.mkdtemp(prefix='adaptive13-sandwich-postmerge-'));lib=w/'lib';lib.mkdir();logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py');providers=[]
for f in (parent/'lib').rglob('*'):
 if f.is_file():
  rel=f.relative_to(parent/'lib')
  if rel.parent==Path('DiophantineConsistency') and rel.name.split('.')[0] in names:continue
  dest=lib/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(f.resolve());providers.append({'path':str(f),'sha256':sha(f),'bytes':f.stat().st_size})
rel=Path('Mathlib/Data/ZMod/Basic.olean');first=next(Path(x)/rel for x in boundary if (Path(x)/rel).is_file());providers.append({'path':str(first),'sha256':sha(first),'bytes':first.stat().st_size})
src=R/'.lake/packages/mathlib/Mathlib/Data/ZMod/Basic.lean';providers.append({'path':str(src),'sha256':sha(src),'bytes':src.stat().st_size})
(w/'providers.json').write_text(json.dumps(providers,indent=2)+'\n')
for n in names:shutil.copyfile(S/(n+'.lean'),logs/(n+'.lean'))
state={'status':'RUNNING','private':str(w),'snapshots':{n:sha(logs/(n+'.lean')) for n in names},'records':[],'providers_sha256':sha(w/'providers.json'),'parent_state_sha256':sha(parent/'state.json'),'pell_state_sha256':sha(pell/'state.json'),'boundary':boundary,'poprefresh_state_sha256':sha(poprefresh/'state.json'),'winrefresh_state_sha256':sha(winrefresh/'state.json'),'scope':'Sandwich, HalfBinomial, population, window and reverse-construction suffix over a previously compiled 17-module provider whose final source reauthentication failed because Sandwich changed; Pell recurrence authenticated separately'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True);env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*boundary]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
try:
 for n in names:
  src=S/(n+'.lean');assert sha(src)==state['snapshots'][n];assert shutil.disk_usage('/tmp').free>=512*1024**2
  out=lib/'DiophantineConsistency'/(n+'.olean');assert not out.exists();log=logs/(n+'.log');tim=logs/(n+'.time');cmd=['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',n,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'name':n,'command':cmd,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim)}
  if out.exists():row['object_sha256']=sha(out)
  state['records'].append(row);save();print('DONE',n,code,round(row['seconds'],2),flush=True);print(log.read_text(),flush=True)
  if code:raise RuntimeError(n)
  assert sha(src)==state['snapshots'][n]
 for x in providers:assert sha(x['path'])==x['sha256']
 for n in names:assert sha(S/(n+'.lean'))==state['snapshots'][n]
 for r in pstate['records']:
  if r['name'] not in names:assert sha(S/(r['name']+'.lean'))==r['source_sha256']
 assert sha(S/'ArithmeticPellRecurrence.lean')==pr['source_sha256']
 for r in popstate['records']:
  if r['name'] not in names and r['name']!='ArithmeticBinomLegendre':assert sha(S/(r['name']+'.lean'))==r['source_sha256']
 for r in winstate['records']:
  if r['name'] not in names and r['name']!='ArithmeticCarrierRadix2011':assert sha(roots[r['namespace']]/(r['name']+'.lean'))==r['source_sha256']
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
