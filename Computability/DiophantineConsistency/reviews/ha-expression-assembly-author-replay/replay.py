from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, tempfile, time
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
SRC=ROOT/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
NAMES=['HAExpressionAssembly','HAExpressionAssemblyChecks']
DIRECT=['HACurrentAssembly2011','ArithmeticCurrentSentence2011']
p=argparse.ArgumentParser();p.add_argument('--parent',type=Path,required=True);p.add_argument('--expected',type=Path);args=p.parse_args();parent=args.parent.resolve()
out=Path(tempfile.mkdtemp(prefix='ha-expression-assembly-'));lib=out/'lib';logs=out/'logs';lib.mkdir();logs.mkdir()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
state={'status':'RUNNING','phase':'initialization','root':str(out),'parent':str(parent),'records':[], 'qualification':'Focused two-module source replay. Direct import object hashes are authenticated, but their source provenance and all transitive HA/ZFC, Foundation, Mathlib and other dependency closures are inherited historical artifacts, not source-current audited. The theorem assumes an all-IΣ₁-model machine bridge and is not an 87-equation proof.'}
def save():
 q=out/'state.json.tmp';q.write_text(json.dumps(state,indent=2,ensure_ascii=False)+'\n');q.replace(out/'state.json')
def require(p,h,label):
 if not p.is_file() or sha(p)!=h:raise RuntimeError(f'{label} missing or changed: {p}')
print('ROOT',out,flush=True);save()
try:
 expected=json.loads(args.expected.read_text()) if args.expected else None
 state['phase']='authenticate inputs';save()
 initial={n:sha(SRC/(n+'.lean')) for n in NAMES}
 direct={n:sha(parent/'DiophantineConsistency'/(n+'.olean')) for n in DIRECT}
 state['input_sources']=initial;state['direct_import_objects']=direct;save()
 if expected:
  if initial!=expected['input_sources']:raise RuntimeError('source snapshot differs from author')
  if direct!=expected['direct_import_objects']:raise RuntimeError('direct import hashes differ from author')
 for path in parent.iterdir():
  if path.name!='DiophantineConsistency':(lib/path.name).symlink_to(path.resolve(),target_is_directory=path.is_dir())
 dst=lib/'DiophantineConsistency';dst.mkdir()
 for path in (parent/'DiophantineConsistency').glob('*.olean'):
  if path.stem not in NAMES:(dst/path.name).symlink_to(path.resolve())
 search=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip();env=dict(os.environ,LEAN_PATH=str(lib)+':'+search,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['LEAN_PATH']=env['LEAN_PATH'];save()
 for n in NAMES:
  state['phase']='compile';state['module']=n;save();src=SRC/(n+'.lean');snap=logs/(n+'.lean');shutil.copyfile(src,snap);obj=dst/(n+'.olean');log=logs/(n+'.log');cmd=['lean','-M8000','-j1','-DElab.async=false',str(src),'-o',str(obj)];t=time.monotonic();r=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log.write_text(r.stdout);row={'module':n,'exit':r.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(src),'object_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log),'command':cmd};state['records'].append(row);save()
  if r.returncode or re.search(r'\b(?:warning|error|sorryAx)\b',r.stdout):raise RuntimeError(f'{n} failed: {r.stdout}')
  require(snap,initial[n],'source snapshot')
  if expected:
   exp=next(x for x in expected['records'] if x['module']==n)
   for k in ('source_sha256','object_sha256','log_sha256'):
    if row[k]!=exp[k]:raise RuntimeError(f'{n} {k} differs from author')
  print(n,'PASS',flush=True)
 state['phase']='final authentication';save()
 for n,h in initial.items():require(SRC/(n+'.lean'),h,'source')
 for n,h in direct.items():require(parent/'DiophantineConsistency'/(n+'.olean'),h,'direct import')
 state['status']='PASS';state['phase']='complete';state['module']=None;save();print('PASS',out,flush=True)
except BaseException as exc:
 state['status']='FAILED';state['failure']={'type':type(exc).__name__,'message':str(exc),'phase':state.get('phase'),'module':state.get('module')};save();print('FAILED',out,state['failure'],flush=True);raise
