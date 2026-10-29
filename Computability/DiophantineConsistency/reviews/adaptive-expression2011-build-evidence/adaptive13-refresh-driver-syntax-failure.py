import json,hashlib,pathlib,tempfile,shutil,os,subprocess,time
R=pathlib.Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';P=D/'research/adaptive-expression2011-cache-plan.json'
def h(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert h(P)=='f8ce7569b263e774e84c106cfa8b8e2797792c74c43e006d064f22f14d0c5202'
p=json.loads(P.read_text());assert p['counts']['fresh_prerequisites']==24
for x in p['pins']:assert h(x['path'])==x['sha256'],x['path']
assert shutil.disk_usage('/tmp').free>512*1024**2
w=pathlib.Path(tempfile.mkdtemp(prefix='adaptive13-refresh-'));lib=w/'lib';lib.mkdir();logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py')
(w/'plan.json').write_bytes(P.read_bytes());(w/'state.json').write_text(json.dumps({'status':'PREPARING','records':[]},indent=2));print('PRIVATE',w,flush=True)
for m in p['modules']:
 if m['mode'].startswith('REUSE'):
  for obj in m['selected_objects']:
   t=lib/pathlib.Path(*m['module'].split('.')).with_suffix('.olean');t.parent.mkdir(parents=True,exist_ok=True);t.symlink_to(pathlib.Path(obj['path']).resolve())
mods={m['module']:m for m in p['modules']};env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*p['boundary_search']],LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state={'status':'RUNNING','records':[],'private':str(w)}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save()
try:
 for name in p['fresh_prerequisites']:
  m=mods[name];src=pathlib.Path(m['source']['path']);assert h(src)==m['source']['sha256'];assert shutil.disk_usage('/tmp').free>512*1024**2
  snap=logs/(name+'.lean');shutil.copyfile(src,snap);out=lib/pathlib.Path(*name.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists() and not out.is_symlink()
  log=logs/(name+'.log');timing=logs/(name+'.time');cmd=[p['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',name,flush=True);start=time.monotonic()
  with log.open('w') as f:ret=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],env=env,cwd=R,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'module':name,'source_sha256':h(src),'snapshot_sha256':h(snap),'command':cmd,'exit':ret,'seconds':time.monotonic()-start,'log_sha256':h(log),'time_sha256':h(timing)}
  if out.exists():row['object_sha256']=h(out)
  state['records'].append(row);save();print('DONE',name,ret,round(row['seconds'],1),flush=True)
  if ret: print(log.read_text(),flush=True);raise RuntimeError(name)
  assert h(src)==m['source']['sha256']
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:
 state['status']='FAILED';state['failure']=str(e);save();raise
