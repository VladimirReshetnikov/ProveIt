#!/usr/bin/env python3
"""Replay the literal fourteen-variable no-zero client on audited providers."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,tempfile,time
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs');SRC=ROOT/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--parent',required=True,type=Path);ap.add_argument('--closure',required=True,type=Path);ap.add_argument('--ha-parent',required=True,type=Path);args=ap.parse_args();parent=args.parent.resolve();cl=args.closure.resolve();ha=args.ha_parent.resolve();root=Path(tempfile.mkdtemp(prefix='pra-literal-current-nozero-independent-'));state={'status':'RUNNING','root':str(root),'pra_parent':str(parent),'source_closure_parent':str(cl),'historical_ha_parent':str(ha),'records':[],'phase':'initialization','module':None}
def save():
 p=root/'state.json';q=root/'state.json.tmp';q.write_text(json.dumps(state,indent=2)+'\n');q.replace(p)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(p,h,why):
 if not p.is_file():raise RuntimeError(f'{why} missing: {p}')
 if sha(p)!=h:raise RuntimeError(f'{why} hash differs: {p}')
save();print('ROOT',root,flush=True)
try:
 m=json.loads((HERE/'manifest.json').read_text());names=m['order'];state['qualification']=m['qualification'];state['phase']='authenticate inputs';save()
 def auth():
  for n,r in m['parent_modules'].items():require(SRC/(n+'.lean'),r['source_sha256'],'PRA source');require(parent/'DiophantineConsistency'/(n+'.olean'),r['object_sha256'],'PRA object')
  for n,r in m['closure_modules'].items():require(ROOT/r['source'],r['source_sha256'],'closure source');require(cl/(n.replace('.','/')+'.olean'),r['object_sha256'],'closure object')
  for n,r in m['modules'].items():require(SRC/(n+'.lean'),r['source_sha256'],'client source')
 auth();lib=root/'lib';lib.mkdir();dst=lib/'DiophantineConsistency';dst.mkdir();logs=root/'logs';logs.mkdir();(lib/'Foundation').symlink_to((parent/'Foundation').resolve(),target_is_directory=True)
 for f in (parent/'DiophantineConsistency').glob('*.olean'):
  if f.stem not in names:(dst/f.name).symlink_to(f.resolve())
 for n,r in m['closure_modules'].items():
  source=cl/(n.replace('.','/')+'.olean');target=lib/(n.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
  if target.exists():raise RuntimeError(f'unexpected provider overlap: {n}')
  target.symlink_to(source.resolve())
 for d in ha.iterdir():
  if d.is_dir() and d.name not in ['DiophantineConsistency','Foundation','BusyBeaver'] and not (lib/d.name).exists():(lib/d.name).symlink_to(d.resolve(),target_is_directory=True)
 search=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip();env=dict(os.environ,LEAN_PATH=str(lib)+':'+search,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['LEAN_PATH']=env['LEAN_PATH'];save()
 for n in names:
  state['phase']='compile';state['module']=n;save();src=SRC/(n+'.lean');snap=logs/(n+'.lean');snap.write_bytes(src.read_bytes());obj=dst/(n+'.olean');log=logs/(n+'.log');cmd=['lean','-M6000','-j1','-DElab.async=false',str(src),'-o',str(obj)];t=time.monotonic();p=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log.write_text(p.stdout);row={'module':n,'exit':p.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(src),'object_sha256':sha(obj) if obj.is_file() else None,'log_sha256':sha(log),'command':cmd};state['records'].append(row);save()
  if p.returncode or re.search(r'\b(?:warning|error|sorryAx)\b',p.stdout):raise RuntimeError(f'{n} compilation failed: {p.stdout}')
  require(src,m['modules'][n]['source_sha256'],'source');require(snap,m['modules'][n]['source_sha256'],'snapshot');require(obj,m['modules'][n]['object_sha256'],'object');require(log,m['modules'][n]['log_sha256'],'full log');print(n,'PASS',flush=True)
 state['phase']='final authentication';save();auth()
 for n,r in m['modules'].items():require(dst/(n+'.olean'),r['object_sha256'],'final object')
 state['status']='PASS';state['phase']='complete';state['module']=None;save();print('PASS',root,flush=True)
except BaseException as exc:
 state['status']='FAILED';state['failure']={'type':type(exc).__name__,'message':str(exc),'phase':state.get('phase'),'module':state.get('module')};save();print('FAILED',root,state['failure'],flush=True);raise
