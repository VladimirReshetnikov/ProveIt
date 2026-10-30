#!/usr/bin/env python3
"""Rebuild literal strict-surrogate/forward clients over audited parents.

The inherited HACurrentEquation2011 object and its full HA/IΣ₁ closure are
historical: this script does not authenticate them. See state qualification.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, tempfile, time
ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
HERE = Path(__file__).resolve().parent
SRC = ROOT / 'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
REV = ROOT / 'Computability/DiophantineConsistency/reviews'
NAMES = ['PRACurrentStrictCon', 'PRACurrentStrictConChecks', 'PRACurrentConsistencyForward', 'PRACurrentConsistencyForwardChecks']
a = argparse.ArgumentParser(); a.add_argument('--parent', type=Path, required=True); a.add_argument('--closure', type=Path, required=True); a.add_argument('--expected', type=Path)
args = a.parse_args(); parent = args.parent.resolve(); closure = args.closure.resolve()
out = Path(tempfile.mkdtemp(prefix='pra-literal-forward-focused-')); lib = out/'lib'; logs = out/'logs'; lib.mkdir(); logs.mkdir()
state = {'status':'RUNNING','phase':'initialization','root':str(out),'parent':str(parent),'closure':str(closure),'qualification':'Focused replay of four clients with exact generic parent and 26-module no-zero closure authenticated. HACurrentEquation2011 and its transitive IΣ₁/HA endpoint are inherited historical artifacts, not source-current audited; Foundation/Mathlib/PAHF and other unlisted dependencies are inherited. Only literal Con→no-zero is shown; reverse remains open.','records':[]}
def save():
 t=out/'state.json.tmp'; t.write_text(json.dumps(state,indent=2)+'\n'); t.replace(out/'state.json')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(p,h,why):
 if not p.is_file() or sha(p)!=h: raise RuntimeError(f'{why} missing or hash mismatch: {p}')
def link(src,dst):
 dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.is_symlink() or dst.exists(): dst.unlink()
 dst.symlink_to(src.resolve())
print('ROOT',out,flush=True); save()
try:
 pm=json.loads((REV/'pra-strict-surrogate-postmerge-author-replay/manifest.json').read_text())
 cm=json.loads((REV/'pra-current-nozero-closure-author-replay/manifest.json').read_text())
 initial={n:sha(SRC/(n+'.lean')) for n in NAMES}; inherited=closure/'DiophantineConsistency/HACurrentEquation2011.olean'
 state['historical_endpoint']={'path':str(inherited.resolve()),'object_sha256':sha(inherited)}; state['input_sources']=initial
 def auth():
  for group in ('parent_modules','modules'):
   for n,v in pm[group].items(): require(SRC/(n+'.lean'),v['source_sha256'],'generic parent source'); require(parent/'DiophantineConsistency'/(n+'.olean'),v['object_sha256'],'generic parent object')
  for v in cm['order']:
   require(ROOT/v['source'],v['source_sha256'],'no-zero closure source'); require(closure/(v['module'].replace('.','/')+'.olean'),v['object_sha256'],'no-zero closure object')
  for n,h in initial.items(): require(SRC/(n+'.lean'),h,'client source')
  require(inherited,state['historical_endpoint']['object_sha256'],'historical IΣ₁ endpoint object')
 state['phase']='authenticate inputs';save();auth()
 # Inherit all historical objects, replace the PRA provider objects, then use
 # the independently rebuilt 26-module no-zero objects for their exact names.
 for path in closure.rglob('*.olean'):
  link(path,lib/path.relative_to(closure))
 for path in parent.rglob('*.olean'):
  link(path,lib/path.relative_to(parent))
 for v in cm['order']:
  rel=Path(v['module'].replace('.','/')+'.olean');link(closure/rel,lib/rel)
 for n in NAMES:
  p=lib/'DiophantineConsistency'/(n+'.olean')
  if p.is_symlink() or p.exists(): p.unlink()
 for p in closure.iterdir():
  if p.name=='Foundation' and not (lib/p.name).exists(): (lib/p.name).symlink_to(p.resolve(),target_is_directory=True)
 search=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip(); env=dict(os.environ,LEAN_PATH=str(lib)+':'+search,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['LEAN_PATH']=env['LEAN_PATH'];save()
 expected=json.loads(args.expected.read_text()) if args.expected else None
 for n in NAMES:
  state['phase']='compile';state['module']=n;save();src=SRC/(n+'.lean');snap=logs/(n+'.lean');shutil.copyfile(src,snap);obj=lib/'DiophantineConsistency'/(n+'.olean');log=logs/(n+'.log');cmd=['lean','-M8000','-j1','-DElab.async=false',str(src),'-o',str(obj)];t=time.monotonic();p=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log.write_text(p.stdout); row={'module':n,'exit':p.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(src),'object_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log),'command':cmd};state['records'].append(row);save()
  if p.returncode or re.search(r'\b(?:warning|error|sorryAx)\b',p.stdout): raise RuntimeError(f'{n} failed: {p.stdout}')
  require(snap,initial[n],'client snapshot')
  if expected:
   exp=next(x for x in expected['records'] if x['module']==n)
   for k in ('source_sha256','object_sha256','log_sha256'):
    if row[k]!=exp[k]: raise RuntimeError(f'{n} {k} differs from author')
  print(n,'PASS',flush=True)
 state['phase']='final authentication';save();auth();state['status']='PASS';state['phase']='complete';state['module']=None;save();print('PASS',out,flush=True)
except BaseException as e:
 state['status']='FAILED';state['failure']={'type':type(e).__name__,'message':str(e),'phase':state.get('phase'),'module':state.get('module')};save();print('FAILED',out,state['failure'],flush=True);raise
