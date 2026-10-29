from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=Path('/tmp/adaptive13-cache-boundary-dense-e9vq2dll');L=Path('/tmp/adaptive13-cache-boundary-light-2fh6hyb2');C=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');roots={'DiophantineConsistency':R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency','BusyBeaver':R/'Computability/BusyBeaver/Lean/BusyBeaver'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
bs=read(B/'state.json');ls=read(L/'state.json');cs=read(C/'state.json');assert bs['status']=='PASS' and ls['status']=='PASS_FIVE' and cs['status']=='PASS';guard=read(C/'guards.json');assert sha(C/'guards.json')==cs['guards_sha256'];assert all(sha(p)==h for p,h in guard.items())
for r in ls['records']:assert sha(roots[r['namespace']]/(r['name']+'.lean'))==r['source_sha256'] and sha(B/'lib'/r['namespace']/(r['name']+'.olean'))==r['object_sha256']
assert sha(roots['BusyBeaver']/'ZFC/KDense215.lean')==bs['source_sha256'] and sha(B/'lib/BusyBeaver/ZFC/KDense215.olean')==bs['object_sha256']
ns='DiophantineConsistency';n='DecimalMachine215';key=ns+'.'+n;src=roots[ns]/(n+'.lean');assert sha(src)==ls['snapshots'][key];assert shutil.disk_usage('/tmp').free>=512*1024**2
w=Path(tempfile.mkdtemp(prefix='adaptive13-cache-boundary-decimal-'));lib=w/'lib';lib.mkdir();shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(src,w/'DecimalMachine215.lean');providers=[]
for f in (B/'lib').rglob('*'):
 if f.is_file():
  rel=f.relative_to(B/'lib');dest=lib/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(f.resolve());providers.append({'path':str(f),'sha256':sha(f),'bytes':f.stat().st_size})
(w/'providers.json').write_text(json.dumps(providers,indent=2)+'\n');state={'status':'RUNNING','private':str(w),'source_sha256':sha(src),'previous_object_sha256':ls['previous_objects'][key],'providers_sha256':sha(w/'providers.json'),'dense_state_sha256':sha(B/'state.json'),'light_state_sha256':sha(L/'state.json'),'canonical_state_sha256':sha(C/'state.json'),'canonical_guards_sha256':sha(C/'guards.json'),'scope':'isolated DecimalMachine215 rebuild after six source-rebuilt prerequisites; not accepted into canonical composition','boundary':bs['boundary']}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True);out=lib/ns/(n+'.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists();env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M2000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',key,flush=True);start=time.monotonic()
try:
 with (w/'build.log').open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(w/'build.time'),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 state.update(exit=code,command=cmd,seconds=time.monotonic()-start,log_sha256=sha(w/'build.log'),time_sha256=sha(w/'build.time'))
 if out.exists():state.update(object_sha256=sha(out),matches_previous=sha(out)==state['previous_object_sha256'])
 save();print('DONE',code,round(state['seconds'],2),'matches previous',state.get('matches_previous'),flush=True);print((w/'build.log').read_text(),flush=True)
 if code:raise RuntimeError(key)
 for x in providers:assert sha(x['path'])==x['sha256']
 for p,h in guard.items():assert sha(p)==h
 assert sha(src)==state['source_sha256'] and sha(B/'state.json')==state['dense_state_sha256'] and sha(L/'state.json')==state['light_state_sha256'] and sha(C/'state.json')==state['canonical_state_sha256']
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
