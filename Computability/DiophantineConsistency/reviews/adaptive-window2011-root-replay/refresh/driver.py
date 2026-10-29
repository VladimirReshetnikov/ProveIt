from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs'); DC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';A=Path('/tmp/adaptive13-population-zmsxzr6g')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
sa=json.loads((A/'state.json').read_text());assert sa['status']=='PASS'
for x in sa['records']:
 assert sha(DC/(x['name']+'.lean'))==x['source_sha256'];assert sha(A/'lib/DiophantineConsistency'/(x['name']+'.olean'))==x['object_sha256']
S={'DiophantineConsistency':DC,'FirstOrder':R/'Logic/FirstOrder/Lean/FirstOrder','PAHF':R/'Logic/Interpretability/PAHF/Lean/PAHF'}
seen=set();order=[]
def visit(ns,n):
 k=(ns,n)
 if k in seen:return
 seen.add(k);f=S[ns]/(n+'.lean');assert f.is_file(),str(f)
 for line in f.read_text().splitlines():
  m=re.match(r'^import (DiophantineConsistency|FirstOrder|PAHF)\.([\w.]+)',line)
  if m:visit(m.group(1),m.group(2).replace('.','/'))
 if not (A/'lib'/ns/(n+'.olean')).is_file():order.append(k)
visit('DiophantineConsistency','ArithmeticAdaptiveWindowCore2011')
expected={'ArithmeticNegativeNorms','HAProofs','ArithmeticExpression','CurrentEquationSyntax2011','ArithmeticCarrierSoundness2011','ArithmeticCarrierRadix2011','ArithmeticStandardCasts','ArithmeticRepunit','ArithmeticBinaryCarry','ArithmeticWindowDigits','ArithmeticMaskData','ArithmeticMaskKernel','ArithmeticMaskConstants','ArithmeticMaskPopulation','ArithmeticSaturation','ArithmeticWindowBits','ArithmeticCyclicWord','ArithmeticWindowCarry','ArithmeticWindowInterface','ArithmeticAdaptiveWindowCore2011'}
assert {n for ns,n in order if ns=='DiophantineConsistency'}==expected,order
assert {(ns,n) for ns,n in order if ns!='DiophantineConsistency'}=={('FirstOrder','Fol'),('FirstOrder','Calculus'),('FirstOrder','Completeness'),('PAHF','AckermannHFCore'),('PAHF','PACore')},order
assert shutil.disk_usage('/tmp').free>=512*1024**2
w=Path(tempfile.mkdtemp(prefix='adaptive13-window-refresh-'));lib=w/'lib';lib.mkdir();logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py');providers={}
for f in (A/'lib').rglob('*'):
 if f.is_file():
  rel=f.relative_to(A/'lib');dest=lib/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(f.resolve());providers[str(f)]=sha(f)
for ns,n in order:
 dest=logs/ns/(n+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(S[ns]/(n+'.lean'),dest)
(w/'providers.json').write_text(json.dumps(providers,indent=2)+'\n');p=json.loads(Path('/tmp/arithmetic-signed-pairs-peer-f4gz2l0f/inputs.json').read_text());boundary=p['LEAN_PATH'][1:];assert all('/.lake/packages/' in x or '/toolchains/' in x for x in boundary)
state={'status':'RUNNING','private':str(w),'order':[ns+'.'+n for ns,n in order],'snapshots':{ns+'.'+n:sha(logs/ns/(n+'.lean')) for ns,n in order},'records':[],'providers_sha256':sha(w/'providers.json'),'parent_state_sha256':sha(A/'state.json')}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,'ORDER',state['order'],flush=True);env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*boundary]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
try:
 for ns,n in order:
  key=ns+'.'+n;src=S[ns]/(n+'.lean');assert sha(src)==state['snapshots'][key];assert shutil.disk_usage('/tmp').free>=512*1024**2
  out=lib/ns/(n+'.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists();log=logs/ns/(n+'.log');tim=logs/ns/(n+'.time');cmd=['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',key,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'name':n,'namespace':ns,'command':cmd,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim)}
  if out.exists():row['object_sha256']=sha(out)
  state['records'].append(row);save();print('DONE',key,code,round(row['seconds'],2),flush=True);print(log.read_text(),flush=True)
  if code:raise RuntimeError(key)
  assert sha(src)==state['snapshots'][key]
 for f,h in providers.items():assert sha(f)==h
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
