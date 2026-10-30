from pathlib import Path
import json,hashlib,subprocess,os,time,re,tempfile
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';packet=R/'Computability/DiophantineConsistency/reviews/pra-formulaset-commonpair-author-replay/baseline.json';parent=Path('/tmp/pra-commonpair-overlay-h2rccnvo/lib');sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest();root=Path(tempfile.mkdtemp(prefix='pra-formulaset-commonpair-'));state={'status':'RUNNING','root':str(root),'parent':str(parent),'phase':'initialization','module':None,'records':[]}
def save():
 p=root/'state.json';q=root/'state.json.tmp';q.write_text(json.dumps(state,indent=2)+'\n');q.replace(p)
save();print('ROOT',root,flush=True)
try:
 state['phase']='graph audit';save();man=json.loads(packet.read_text());known=man['parent_modules']|man['modules'];seen=set();affected=set();order=[];allorder=[];depsmap={};initial={};changed=[]
 def visit(n):
  if n in seen:return
  seen.add(n);p=S/(n+'.lean');deps=[];initial[n]=sha(p)
  for l in p.read_text().splitlines():
   if l.startswith('import DiophantineConsistency.'):
    for x in l.split()[1:]:
     if x.startswith('DiophantineConsistency.'):deps.append(x.rsplit('.',1)[1]);visit(deps[-1])
  depsmap[n]=deps;allorder.append(n)
  if initial[n]!=known.get(n,{}).get('source_sha256'):
   changed.append(n)
  obj=parent/'DiophantineConsistency'/(n+'.olean')
  object_ok=obj.is_file() and sha(obj)==known.get(n,{}).get('object_sha256')
  if initial[n]!=known.get(n,{}).get('source_sha256') or not object_ok or any(d in affected for d in deps):affected.add(n);order.append(n)
 targets=['PRAFormulaSetCommonPairBoundChecks']
 for n in targets:visit(n)
 state.update({'order':order,'allorder':allorder,'deps':depsmap,'changed_or_new':changed,'initial_source_sha256':initial});save();print('MODULES',len(order),'CHANGED',changed,flush=True)
 state['phase']='authenticate parent';save()
 for n in allorder:
  state['module']=n
  if n not in affected:
   obj=parent/'DiophantineConsistency'/(n+'.olean')
   if n not in known or not obj.is_file() or sha(obj)!=known[n]['object_sha256']:raise RuntimeError('unverified parent '+str(obj))
 state['module']=None;state['phase']='prepare overlay';save();lib=root/'lib';lib.mkdir();dst=lib/'DiophantineConsistency';dst.mkdir();logs=root/'logs';logs.mkdir();foundation=parent/'Foundation'
 if not foundation.is_dir():raise RuntimeError('Foundation missing '+str(foundation))
 (lib/'Foundation').symlink_to(foundation.resolve(),target_is_directory=True)
 for f in (parent/'DiophantineConsistency').glob('*.olean'):
  if f.stem not in affected:(dst/f.name).symlink_to(f.resolve())
 base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=R,text=True).strip();env=dict(os.environ,LEAN_PATH=str(lib)+':'+base,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['LEAN_PATH']=env['LEAN_PATH'];save()
 for n in order:
  state['phase']='compile';state['module']=n;save();src=S/(n+'.lean');snap=logs/(n+'.lean')
  if sha(src)!=initial[n]:raise RuntimeError('source changed before build: '+n)
  snap.write_bytes(src.read_bytes());obj=dst/(n+'.olean');cmd=['lean','-M6000','-j1','-DElab.async=false',str(src),'-o',str(obj)];t=time.monotonic();p=subprocess.run(cmd,cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log=logs/(n+'.log');log.write_text(p.stdout);row={'module':n,'exit':p.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(src),'object_sha256':sha(obj) if obj.is_file() else None,'log_sha256':sha(log),'command':cmd};state['records'].append(row);save();print(n,p.returncode,round(row['seconds'],1),flush=True)
  if p.returncode or re.search(r'\b(?:warning|error|sorryAx)\b',p.stdout):raise RuntimeError(f'compile failed or forbidden diagnostic in {n}, exit {p.returncode}, log {log}:\n{p.stdout}')
  if sha(snap)!=initial[n] or sha(src)!=initial[n]:raise RuntimeError('source changed during build: '+n)
 state['phase']='final graph authentication';save()
 for n in allorder:
  state['module']=n
  if sha(S/(n+'.lean'))!=initial[n]:raise RuntimeError('source changed during build: '+n)
  if n not in affected and sha(parent/'DiophantineConsistency'/(n+'.olean'))!=known[n]['object_sha256']:raise RuntimeError('parent object changed during build: '+n)
 state['phase']='complete';state['module']=None;state['status']='PASS';save();print('PASS',root,flush=True)
except BaseException as exc:
 state['status']='FAILED';state['failure']={'type':type(exc).__name__,'message':str(exc),'phase':state.get('phase'),'module':state.get('module')};save();print('FAILED',root,state['failure'],flush=True);raise
