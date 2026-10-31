from pathlib import Path
import os,re,subprocess,hashlib,json,tempfile,time,sys
repo=Path.cwd();source=repo/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';parent=Path('/tmp/pra-history-set-term-result-lh70f470/lib')
work=Path(tempfile.mkdtemp(prefix='pra-setshift-full-project-'));src=work/'src/DiophantineConsistency';src.mkdir(parents=True);lib=work/'lib';dest=lib/'DiophantineConsistency';dest.mkdir(parents=True);logs=work/'logs';logs.mkdir()
for name in ('Foundation','ZFCinPA'):(lib/name).symlink_to((parent/name).resolve(),target_is_directory=True)
seen=set();order=[];deps={}; hashes={}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(n):
 if n in seen:return
 seen.add(n);f=source/(n+'.lean');data=f.read_bytes();(src/(n+'.lean')).write_bytes(data);hashes[n]=hashlib.sha256(data).hexdigest();ds=re.findall(r'^import DiophantineConsistency\.(\w+)',data.decode(),re.M);deps[n]=ds
 for d in ds:rec(d)
 order.append(n)
rec('PRAWitnessCodeGrowth')
# A source snapshot, not a live-source guard: preserve coherent pre-merge inputs.
assert all(sha(src/(n+'.lean'))==h for n,h in hashes.items())
base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip().split(':')
base=[x for x in base if not x.startswith(str(repo/'.lake/build/lib/lean'))]
env=dict(os.environ,LEAN_PATH=str(lib)+':'+':'.join(base),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
state={'status':'RUNNING','root':str(work),'parent':str(parent),'order':order,'deps':deps,'snapshot_source_sha256':hashes,'records':[],'scope':'All declared local project imports rebuilt from frozen source snapshot. Foundation, ZFCinPA, mathlib, toolchain and package ancestry inherited; no claim of current workspace source identity after snapshot or full external closure authentication.'}
def save():
 (work/'state.tmp').write_text(json.dumps(state,indent=2)+'\n');(work/'state.tmp').replace(work/'state.json')
save();print('ROOT',work,'modules',len(order),flush=True)
try:
 for n in order:
  state['module']=n;save();f=src/(n+'.lean');obj=dest/(n+'.olean');log=logs/(n+'.log');t=time.monotonic()
  with log.open('w') as o:r=subprocess.run(['lean','-M6000','-j1','-DElab.async=false','--root='+str(src.parent),str(f),'-o',str(obj)],cwd=repo,env=env,stdout=o,stderr=subprocess.STDOUT)
  row={'module':n,'exit':r.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(f),'object_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log)};state['records'].append(row);save()
  if r.returncode!=0 or re.search(r'\b(?:warning|error|sorryAx)\b',log.read_text()):raise RuntimeError('failed '+n)
  print('PASS',n,flush=True)
 assert all(sha(src/(n+'.lean'))==h for n,h in hashes.items())
 state.update(status='PASS',module=None);save();print('PASS',work,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();print('FAILED',repr(e),flush=True);raise
