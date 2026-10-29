from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';P=Path('/tmp/adaptive13-ranklower-postmerge-tjqelwlk');audit=Path('/tmp/adaptive13-assembly-pell-audit.json');audit_driver=Path('/tmp/adaptive13-assembly-pell-audit.py')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
names=['ArithmeticOuterSeed','ArithmeticPellSquaredSeed','ArithmeticPellSquaredSeedChecks','ArithmeticPellAuxiliarySeed','ArithmeticPellAuxiliarySeedChecks','ArithmeticConstructionBoundPell']
ps=read(P/'state.json');assert ps['status']=='PASS'
for r in ps['records']:assert sha(S/(r['name']+'.lean'))==r['source_sha256'] and sha(P/'lib/DiophantineConsistency'/(r['name']+'.olean'))==r['object_sha256']
a=read(audit);assert a['provider_state_sha256']==sha(P/'state.json');assert all(r['provenance']!='unmatched boundary' for r in a['rows'])
for r in a['rows']:
 assert sha(S/(r['module']+'.lean'))==r['source_sha256'];assert sha(P/'lib/DiophantineConsistency'/(r['module']+'.olean'))==r['object_sha256'];assert str((P/'lib/DiophantineConsistency'/(r['module']+'.olean')).resolve())==r['resolved_object']
boundary=ps['boundary'];assert all('/.lake/packages/' in x or '/toolchains/' in x for x in boundary);assert shutil.disk_usage('/tmp').free>=512*1024**2
w=Path(tempfile.mkdtemp(prefix='adaptive13-assembly-pell-'));lib=w/'lib';lib.mkdir();logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(audit,w/'audit.json');shutil.copyfile(audit_driver,w/'audit.py');providers=[]
for f in (P/'lib').rglob('*'):
 if f.is_file():
  rel=f.relative_to(P/'lib')
  if rel.parent==Path('DiophantineConsistency') and rel.name.split('.')[0] in names:continue
  dest=lib/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(f.resolve());providers.append({'path':str(f),'sha256':sha(f),'bytes':f.stat().st_size})
(w/'providers.json').write_text(json.dumps(providers,indent=2)+'\n')
for n in names:shutil.copyfile(S/(n+'.lean'),logs/(n+'.lean'))
state={'status':'RUNNING','private':str(w),'snapshots':{n:sha(logs/(n+'.lean')) for n in names},'records':[],'providers_sha256':sha(w/'providers.json'),'parent_state_sha256':sha(P/'state.json'),'audit_sha256':sha(w/'audit.json'),'boundary':boundary,'scope':'four Assembly Pell prerequisites and two checks; current DiophantineConsistency transitive sources audited, cross-namespace and package internals inherited boundaries'}
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
 for r in a['rows']:assert sha(S/(r['module']+'.lean'))==r['source_sha256'] and sha(P/'lib/DiophantineConsistency'/(r['module']+'.olean'))==r['object_sha256']
 for r in ps['records']:assert sha(S/(r['name']+'.lean'))==r['source_sha256']
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
