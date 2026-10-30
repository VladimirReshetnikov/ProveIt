#!/usr/bin/env python3
"""Replay a focused Foundation conditional derivation core negative-pi bound proof."""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, tempfile, time
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
SRC=ROOT/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(); ap.add_argument('--parent',type=Path,required=True); ap.add_argument('--expected',type=Path); args=ap.parse_args()
parent=args.parent.resolve(); work=Path(tempfile.mkdtemp(prefix='pra-derivation-core-pi-bound-')); logs=work/'logs'; logs.mkdir();lib=work/'lib';lib.mkdir(); dst=lib/'DiophantineConsistency';dst.mkdir()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save():
 q=work/'state.json.tmp';q.write_text(json.dumps(state,indent=2,ensure_ascii=False)+'\n');q.replace(work/'state.json')
def check(path, digest, what):
 if not path.is_file():raise RuntimeError(f'{what} missing: {path}')
 actual=sha(path)
 if actual!=digest:raise RuntimeError(f'{what} differs: {path}; expected {digest}; actual {actual}')
state={'status':'RUNNING','root':str(work),'parent':str(parent),'records':[],'phase':'initialization','module':None};save();print('ROOT',work,flush=True)
try:
 m=json.loads((HERE/'inputs.json').read_text()); names=m['order']; state['qualification']=m['qualification'];state['phase']='authenticate parents';save()
 check(HERE/'parent-manifest.json',m['parent_manifest_sha256'],'Parent manifest');pm=json.loads((HERE/'parent-manifest.json').read_text())
 parent_state=parent.parent/'state.json';state['parent_state_sha256']=sha(parent_state)
 if json.loads(parent_state.read_text())['status']!='PASS':raise RuntimeError('Parent is not PASS')
 def audit():
  check(parent_state,state['parent_state_sha256'],'Parent terminal state')
  for group in ('parent_modules','modules'):
   for n,r in pm[group].items():
    state['module']=n;check(SRC/(n+'.lean'),r['source_sha256'],'Parent source');check(parent/'DiophantineConsistency'/(n+'.olean'),r['object_sha256'],'Parent object')
  for f in m['foundation_files']:
   check(Path(f['source']),f['source_sha256'],'Foundation source');check(parent/f['object'],f['object_sha256'],'Foundation object')
  for n,h in m['sources'].items():state['module']=n;check(SRC/(n+'.lean'),h,'Client source')
 audit();state['module']=None;state['phase']='prepare overlay';save()
 foundation=parent/'Foundation'
 if not foundation.is_dir():raise RuntimeError('Missing inherited Foundation provider')
 (lib/'Foundation').symlink_to(foundation.resolve(),target_is_directory=True)
 for f in (parent/'DiophantineConsistency').glob('*.olean'):
  if f.stem not in names:(dst/f.name).symlink_to(f.resolve())
 search=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip();env=dict(os.environ,LEAN_PATH=str(lib)+':'+search,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['LEAN_PATH']=env['LEAN_PATH'];save()
 for n in names:
  state['phase']='compile';state['module']=n;save();source=SRC/(n+'.lean');snap=logs/(n+'.lean');snap.write_bytes(source.read_bytes());obj=dst/(n+'.olean');log=logs/(n+'.log')
  cmd=['lean','-M6000','-j1','-DElab.async=false',str(source),'-o',str(obj)];start=time.monotonic();p=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log.write_text(p.stdout)
  row={'module':n,'exit':p.returncode,'seconds':time.monotonic()-start,'source_sha256':sha(source),'object_sha256':sha(obj) if obj.is_file() else None,'log_sha256':sha(log),'command':cmd};state['records'].append(row);save()
  if p.returncode or re.search(r'\b(?:warning|error|sorryAx)\b',p.stdout):raise RuntimeError(f'Compilation or diagnostic failure for {n}, full log {log}:\n{p.stdout}')
  check(source,m['sources'][n],'Client source after compilation');check(snap,m['sources'][n],'Client snapshot')
  if args.expected:
   exp=json.loads(args.expected.read_text());rr=next(x for x in exp['records'] if x['module']==n)
   for k in ('source_sha256','object_sha256','log_sha256'):
    if row[k]!=rr[k]:raise RuntimeError(f'{n} {k} differs: expected {rr[k]}, got {row[k]}')
  print(n,'PASS',flush=True)
 state['phase']='final source and provider authentication';state['module']=None;save();audit()
 state['status']='PASS';state['phase']='complete';state['module']=None;save();print('PASS',work,flush=True)
except BaseException as exc:
 state['status']='FAILED';state['failure']={'type':type(exc).__name__,'message':str(exc),'phase':state.get('phase'),'module':state.get('module')};save();print('FAILED',work,state['failure'],flush=True);raise
