#!/usr/bin/env python3
"""Rebuild the exact no-zero source closure on a fresh inherited provider overlay."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,tempfile,time
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--parent',required=True,type=Path);ap.add_argument('--ha-parent',required=True,type=Path);ap.add_argument('--snapshot-root',required=True,type=Path);args=ap.parse_args()
parent=args.parent.resolve();ha=args.ha_parent.resolve();fixedsrc=args.snapshot_root.resolve();root=Path(tempfile.mkdtemp(prefix='pra-current-nozero-closure-samepath-independent-'));state={'status':'RUNNING','root':str(root),'pra_parent':str(parent),'historical_ha_parent':str(ha),'compile_snapshot_root':str(fixedsrc),'records':[],'phase':'initialization','module':None}
def save():
 p=root/'state.json';q=root/'state.json.tmp';q.write_text(json.dumps(state,indent=2)+'\n');q.replace(p)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(p,h,why):
 if not p.is_file():raise RuntimeError(f'{why} missing: {p}')
 x=sha(p)
 if x!=h:raise RuntimeError(f'{why} differs: {p}; expected {h}; actual {x}')
save();print('ROOT',root,flush=True)
try:
 m=json.loads((HERE/'manifest.json').read_text());rows=m['order'];names={r['module'] for r in rows};state['qualification']=m['qualification'];state['phase']='authenticate inputs';save()
 for r in rows:
  require(ROOT/r['source'],r['source_sha256'],'current source');require(fixedsrc/(r['module'].replace('.','/')+'.lean'),r['source_sha256'],'fixed compile snapshot')
 for n,r in m['historical_ha_direct'].items():require(ha/(n.replace('.','/')+'.olean'),r['object_sha256'],'inherited PAHF object')
 lib=root/'lib';lib.mkdir();srcroot=root/'src';srcroot.mkdir();logs=root/'logs';logs.mkdir()
 for provider in [parent,ha]:
  for ns in provider.iterdir():
   if not ns.is_dir():continue
   if ns.name=='Foundation':
    if not (lib/'Foundation').exists():(lib/'Foundation').symlink_to(ns.resolve(),target_is_directory=True)
    continue
   for dr,dirs,files in os.walk(ns,followlinks=False):
    for fn in files:
     if not fn.endswith('.olean'):continue
     f=Path(dr)/fn;rel=f.relative_to(provider);name='.'.join(rel.with_suffix('').parts)
     if name in names:continue
     dst=lib/rel
     if not dst.exists():dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(f.resolve())
 for r in rows:
  snap=srcroot/(r['module'].replace('.','/')+'.lean');snap.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/r['source'],snap);require(snap,r['source_sha256'],'snapshot')
 search=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip();env=dict(os.environ,LEAN_PATH=str(lib)+':'+search,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['LEAN_PATH']=env['LEAN_PATH'];save()
 for r in rows:
  n=r['module'];snap=srcroot/(n.replace('.','/')+'.lean');obj=lib/(n.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);log=logs/(n+'.log');cmd=['lean','-M8000','-j1','-DElab.async=false','-R',str(fixedsrc),str(fixedsrc/(n.replace('.','/')+'.lean')),'-o',str(obj)];state['phase']='compile';state['module']=n;save();start=time.monotonic();p=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log.write_text(p.stdout);canon=p.stdout.replace(str(root),'<BUILD_ROOT>');rec={'module':n,'exit':p.returncode,'seconds':time.monotonic()-start,'source_sha256':sha(snap),'object_sha256':sha(obj) if obj.is_file() else None,'full_log_sha256':sha(log),'canonical_log_sha256':hashlib.sha256(canon.encode()).hexdigest(),'command':cmd};state['records'].append(rec);save()
  if p.returncode or re.search(r'\b(?:error|sorryAx)\b',p.stdout):raise RuntimeError(f'compile failed {n}: {p.stdout}')
  require(obj,r['object_sha256'],'object');require(snap,r['source_sha256'],'snapshot')
  if rec['full_log_sha256']!=r['author_full_log_sha256']:raise RuntimeError(f'full log differs for {n}: {log}')
  print(n,'PASS',flush=True)
 state['phase']='final authentication';save()
 for r in rows:
  require(ROOT/r['source'],r['source_sha256'],'final source');require(fixedsrc/(r['module'].replace('.','/')+'.lean'),r['source_sha256'],'final fixed compile snapshot');require(srcroot/(r['module'].replace('.','/')+'.lean'),r['source_sha256'],'final snapshot');require(lib/(r['module'].replace('.','/')+'.olean'),r['object_sha256'],'final object')
 for n,r in m['historical_ha_direct'].items():require(ha/(n.replace('.','/')+'.olean'),r['object_sha256'],'final PAHF object')
 state['warnings']=[r['module'] for r in state['records'] if re.search(r'\bwarning\b',(logs/(r['module']+'.log')).read_text())];state['status']='PASS';state['phase']='complete';state['module']=None;save();print('PASS',root,'warnings',state['warnings'],flush=True)
except BaseException as exc:
 state['status']='FAILED';state['failure']={'type':type(exc).__name__,'message':str(exc),'phase':state.get('phase'),'module':state.get('module')};save();print('FAILED',root,state['failure'],flush=True);raise
