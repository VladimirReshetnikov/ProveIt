"""Private first downstream source rebuild; no full-interface compatibility claim."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs'); B=Path(os.environ.get('WANG_SPLIT_TABLE','/tmp/adaptive-wang-table-split-b9zuak6s')); C=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl'); P=Path('/tmp/adaptive13-cell-root-parent-wnvsel13'); Q=Path('/tmp/adaptive-wang-chunk-full-src/DiophantineConsistency'); S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticWangPlane.lean'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text())
bs=read(B/'state.json');cs=read(C/'state.json');ps=read(P/'state.json');chunk=Path(bs['chunk_provider']);ck=read(chunk/'state.json');guards=read(C/'guards.json');providers=read(C/'providers.json');assert bs['status']==cs['status']==ck['status']=='PASS'
assert sha(C/'guards.json')==bs['guards_sha256']==cs['guards_sha256'] and sha(C/'providers.json')==bs['providers_sha256']==cs['providers_sha256']
assert sha(S)==ps['snapshots']['DiophantineConsistency.ArithmeticWangPlane']==sha(P/'logs/DiophantineConsistency/ArithmeticWangPlane.lean')
bh=sha(B/'state.json');ph=sha(P/'state.json');ch=sha(chunk/'state.json');obj=B/'lib/DiophantineConsistency/ArithmeticWangTable.olean';assert ch==bs['chunk_state_sha256'] and sha(obj)==bs['object_sha256']
def auth():
 return (sha(B/'state.json')==bh and sha(P/'state.json')==ph and sha(chunk/'state.json')==ch and sha(S)==ps['snapshots']['DiophantineConsistency.ArithmeticWangPlane'] and sha(obj)==bs['object_sha256']
  and sha(C/'guards.json')==bs['guards_sha256'] and sha(C/'providers.json')==bs['providers_sha256']
  and all(sha(p)==h for p,h in guards.items()) and all(sha(x['path'])==x['sha256'] for x in providers.values())
  and all(sha(Q/(r['name']+'.lean'))==r['source_sha256'] and sha(chunk/'lib/DiophantineConsistency'/(r['name']+'.olean'))==r['object_sha256'] and sha(chunk/'logs'/(r['name']+'.log'))==r['log_sha256'] for r in ck['records']))
assert auth(); w=Path(tempfile.mkdtemp(prefix='adaptive-wang-plane-split-'));lib=w/'lib'
for f in (B/'lib').rglob('*'):
 if f.is_file():
  rel=f.relative_to(B/'lib')
  if rel.parent==Path('DiophantineConsistency') and rel.name.startswith('ArithmeticWangPlane.'):continue
  dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(f.resolve())
(w/'logs').mkdir();shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(S,w/'source-snapshot.lean')
state={'status':'RUNNING','private':str(w),'replacement_provider':str(B),'replacement_state_sha256':bh,'replacement_object_sha256':bs['object_sha256'],'historical_prefix_state_sha256':ph,'chunk_state_sha256':ch,'guards_sha256':bs['guards_sha256'],'providers_sha256':bs['providers_sha256'],'source_sha256':sha(S),'boundary':bs['boundary'],'scope':'Private source rebuild of the first direct WangTable importer, against the split replacement and authenticated inherited provider; does not establish full exported interface compatibility, canonical integration, or HA proof.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True);env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);o=lib/'DiophantineConsistency/ArithmeticWangPlane.olean';log=w/'logs/build.log';tim=w/'logs/build.time';cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(o),str(S)];state['command']=cmd;save();print('START',flush=True);start=time.monotonic()
try:
 with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 state.update(exit=code,seconds=time.monotonic()-start,log_sha256=sha(log),time_sha256=sha(tim));
 if o.exists():state['object_sha256']=sha(o)
 save();print('DONE',code,state['seconds'],flush=True)
 if code:raise RuntimeError('Lean build failed')
 if not auth():raise RuntimeError('source or provider authentication failed after build')
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
