#!/usr/bin/env python3
"""Replay the post-merge Herbrand candidate PRA over an authenticated prior PRA provider."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,tempfile,time
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
SRC=ROOT/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--parent',required=True,type=Path);ap.add_argument('--source-dir',type=Path);ap.add_argument('--lean-root',type=Path);args=ap.parse_args()
if args.source_dir:SRC=args.source_dir.resolve()
parent=args.parent.resolve();root=Path(tempfile.mkdtemp(prefix='pra-seqdomain-postmerge-independent-'))
state={'source_dir':str(SRC),'status':'RUNNING','parent':str(parent),'root':str(root),'records':[],'phase':'initialization','module':None}
def save():
    p=root/'state.json';q=root/'state.json.tmp';q.write_text(json.dumps(state,indent=2,ensure_ascii=False)+'\n');q.replace(p)
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check_hash(p,expected,what):
    if not p.is_file(): raise RuntimeError(f'{what} missing: {p}')
    actual=sha(p)
    if actual != expected: raise RuntimeError(f'{what} differs: {p}; expected {expected}; actual {actual}')
save();print('ROOT',root,flush=True)
try:
    state['phase']='read manifest';save();m=json.loads((HERE/'manifest.json').read_text());names=m['order'];state['qualification']=m['qualification'];save()
    state['phase']='authenticate parent';save()
    check_hash(parent.parent/'state.json',m['parent_state_sha256'],'Parent state')
    if json.loads((parent.parent/'state.json').read_text())['status']!='PASS':raise RuntimeError('Parent not PASS')
    for f in m['foundation_files']:
        check_hash(Path(f['source']),f['source_sha256'],'Foundation source');check_hash(parent/f['object'],f['object_sha256'],'Foundation object')
    for n,row in m['parent_modules'].items():
        state['module']=n
        check_hash(SRC/(n+'.lean'),row['source_sha256'],'Parent source')
        check_hash(parent/'DiophantineConsistency'/(n+'.olean'),row['object_sha256'],'Parent object')
    state['phase']='authenticate source';save()
    for n,row in m['modules'].items():
        state['module']=n;check_hash(SRC/(n+'.lean'),row['source_sha256'],'Source')
    state['phase']='prepare overlay';state['module']=None;save()
    lib=root/'lib';lib.mkdir();dst=lib/'DiophantineConsistency';dst.mkdir();logs=root/'logs';logs.mkdir()
    foundation=parent/'Foundation'
    if not foundation.is_dir(): raise RuntimeError(f'Foundation provider missing: {foundation}')
    (lib/'Foundation').symlink_to(foundation.resolve(),target_is_directory=True)
    for f in (parent/'DiophantineConsistency').glob('*.olean'):
        if f.stem not in names:(dst/f.name).symlink_to(f.resolve())
    search=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip()
    env=dict(os.environ,LEAN_PATH=str(lib)+':'+search,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['LEAN_PATH']=env['LEAN_PATH'];save()
    for n in names:
        state['phase']='compile';state['module']=n;save()
        src=SRC/(n+'.lean');snap=logs/(n+'.lean');snap.write_bytes(src.read_bytes());obj=dst/(n+'.olean');log=logs/(n+'.log')
        cmd=['lean','-M6000','-j1','-DElab.async=false']+(['--root='+str(args.lean_root.resolve())] if args.lean_root else [])+[str(src),'-o',str(obj)];t=time.monotonic()
        p=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log.write_text(p.stdout)
        row={'module':n,'exit':p.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(src),'object_sha256':sha(obj) if obj.is_file() else None,'log_sha256':sha(log),'command':cmd};state['records'].append(row);save()
        if p.returncode: raise RuntimeError(f'Compilation failed for {n}, exit {p.returncode}; full log {log}:\n{p.stdout}')
        if re.search(r'\b(?:warning|error|sorryAx)\b',p.stdout): raise RuntimeError(f'Forbidden diagnostic for {n}; full log {log}:\n{p.stdout}')
        state['phase']='authenticate compiled output';save()
        check_hash(src,m['modules'][n]['source_sha256'],'Source after compile');check_hash(snap,m['modules'][n]['source_sha256'],'Source snapshot')
        check_hash(obj,m['modules'][n]['object_sha256'],'Compiled object');check_hash(log,m['modules'][n]['log_sha256'],'Full log')
        print(n,'PASS',flush=True)
    state['phase']='final source and provider authentication';state['module']=None;save()
    for n,row in m['parent_modules'].items():
        state['module']=n;check_hash(SRC/(n+'.lean'),row['source_sha256'],'Final parent source');check_hash(parent/'DiophantineConsistency'/(n+'.olean'),row['object_sha256'],'Final parent object')
    for n,row in m['modules'].items():
        state['module']=n;check_hash(SRC/(n+'.lean'),row['source_sha256'],'Final source');check_hash(dst/(n+'.olean'),row['object_sha256'],'Final object')
    check_hash(parent.parent/'state.json',m['parent_state_sha256'],'Final parent state')
    for f in m['foundation_files']:
        check_hash(Path(f['source']),f['source_sha256'],'Final Foundation source');check_hash(parent/f['object'],f['object_sha256'],'Final Foundation object')
    state['status']='PASS';state['phase']='complete';state['module']=None;save();print('PASS',root,flush=True)
except BaseException as exc:
    state['status']='FAILED';state['failure']={'type':type(exc).__name__,'message':str(exc),'phase':state.get('phase'),'module':state.get('module')};save()
    print('FAILED',root,state['failure'],flush=True)
    raise
