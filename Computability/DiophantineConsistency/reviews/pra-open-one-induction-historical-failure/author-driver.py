from pathlib import Path
import os,subprocess,hashlib,json,re,time,tempfile
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';P=Path('/tmp/pra-foundation-one-induction-independent-bpzpkx87/lib');root=Path(tempfile.mkdtemp(prefix='pra-open-one-induction-current-'));state={'status':'RUNNING','root':str(root),'parent':str(P),'phase':'initialization','module':None,'records':[]}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save():
 q=root/'state.json.tmp';q.write_text(json.dumps(state,indent=2)+'\n');q.replace(root/'state.json')
save();print('ROOT',root,flush=True)
try:
 names=['PRAOpenOneInduction','PRAOpenOneInductionChecks'];initial={n:sha(S/(n+'.lean')) for n in names};state['initial']=initial;state['order']=names
 m=json.loads((R/'Computability/DiophantineConsistency/reviews/pra-foundation-one-induction-current-author-replay/manifest.json').read_text());known=m['parent_modules']|m['modules'];state['phase']='authenticate parent';save()
 for n,row in known.items():
  state['module']=n
  src=S/(n+'.lean');obj=P/'DiophantineConsistency'/(n+'.olean')
  if sha(src)!=row['source_sha256']:raise RuntimeError('parent source differs: '+str(src))
  if not obj.is_file() or sha(obj)!=row['object_sha256']:raise RuntimeError('parent object differs: '+str(obj))
 state['phase']='prepare overlay';state['module']=None;save();L=root/'lib';D=L/'DiophantineConsistency';G=root/'logs';D.mkdir(parents=True);G.mkdir();(L/'Foundation').symlink_to((P/'Foundation').resolve(),target_is_directory=True)
 for f in (P/'DiophantineConsistency').glob('*.olean'):
  if f.stem not in names:(D/f.name).symlink_to(f.resolve())
 env=dict(os.environ,LEAN_PATH=str(L)+':'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=R,text=True).strip(),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['LEAN_PATH']=env['LEAN_PATH'];save()
 for n in names:
  state['phase']='compile';state['module']=n;save();src=S/(n+'.lean');snap=G/(n+'.lean');snap.write_bytes(src.read_bytes());obj=D/(n+'.olean');log=G/(n+'.log');c=['lean','-M6000','-j1','-DElab.async=false',str(src),'-o',str(obj)];start=time.monotonic();p=subprocess.run(c,cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log.write_text(p.stdout);row={'module':n,'exit':p.returncode,'source_sha256':sha(src),'object_sha256':sha(obj) if obj.is_file() else None,'log_sha256':sha(log),'command':c,'seconds':time.monotonic()-start};state['records'].append(row);save();print(n,p.returncode,flush=True)
  if p.returncode or re.search(r'\b(?:warning|error|sorryAx)\b',p.stdout):raise RuntimeError(f'compiler failure or forbidden diagnostic {n}, exit {p.returncode}, log {log}:\n{p.stdout}')
  if sha(src)!=initial[n] or sha(snap)!=initial[n]:raise RuntimeError('source changed during build: '+n)
 state['phase']='final full parent and source audit';save()
 for n,row in known.items():
  state['module']=n
  if sha(S/(n+'.lean'))!=row['source_sha256'] or sha(P/'DiophantineConsistency'/(n+'.olean'))!=row['object_sha256']:raise RuntimeError('parent changed during build: '+n)
 for n in names:
  state['module']=n
  if sha(S/(n+'.lean'))!=initial[n]:raise RuntimeError('source changed during build: '+n)
 state['status']='PASS';state['phase']='complete';state['module']=None;save();print('PASS',root,flush=True)
except BaseException as e:
 state['status']='FAILED';state['failure']={'type':type(e).__name__,'message':str(e),'phase':state['phase'],'module':state['module']};save();print('FAILED',root,state['failure'],flush=True);raise
