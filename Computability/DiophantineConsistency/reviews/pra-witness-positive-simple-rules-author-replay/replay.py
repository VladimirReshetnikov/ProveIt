#!/usr/bin/env python3
"""Focused replay; selected parent object bytes pinned, ancestry inherited."""
from pathlib import Path
import hashlib,json,os,re,subprocess,tempfile,time
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
PARENT=Path('/tmp/pra-positive-simple-parent-w_smy1y_/lib')
PACKET=ROOT/'Computability/DiophantineConsistency/reviews/pra-witness-positive-simple-rules-author-replay'
SOURCE=ROOT/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
MODULES=['PRAWitnessPositiveSimpleRules','PRAWitnessPositiveSimpleRulesChecks']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
root=Path(tempfile.mkdtemp(prefix='pra-witness-positive-simple-rules-'))
state={'status':'RUNNING','phase':'initialization','root':str(root),'records':[]}
def save():
 p=root/'state.json';q=root/'state.json.tmp';q.write_text(json.dumps(state,indent=2)+'\n');q.replace(p)
def must(p,h,why):
 if not p.is_file() or sha(p)!=h: raise RuntimeError(why+': '+str(p))
save();print('ROOT',root,flush=True)
try:
 baseline=json.loads((PACKET/'manifest.json').read_text()); state['phase']='input authentication';save()
 for f,h in baseline['selected_parent_objects'].items():must(PARENT/f,h,'selected parent object')
 for n,h in baseline['sources'].items():must(SOURCE/(n+'.lean'),h,'source')
 for f,h in baseline['direct_source_observations'].items():must(ROOT/f,h,'observed direct source')
 lean=Path(subprocess.check_output(['lake','env','which','lean'],cwd=ROOT,text=True).strip()).resolve();must(lean,baseline['lean_sha256'],'Lean compiler')
 lib=root/'lib';lib.mkdir();dst=lib/'DiophantineConsistency';dst.mkdir();logs=root/'logs';logs.mkdir()
 for f in (PARENT/'DiophantineConsistency').iterdir():
  if f.is_file() and not any(f.name.startswith(n+'.olean') for n in MODULES): (dst/f.name).symlink_to(f.resolve())
 for f in PARENT.iterdir():
  if f.name!='DiophantineConsistency':(lib/f.name).symlink_to(f.resolve(),target_is_directory=f.is_dir())
 base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip();env=dict(os.environ,LEAN_PATH=str(lib)+':'+base,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['LEAN_PATH']=env['LEAN_PATH'];state['parent']=str(PARENT);save()
 for n in MODULES:
  state.update(phase='compile',module=n);save();src=SOURCE/(n+'.lean');must(src,baseline['sources'][n],'source before');snap=logs/(n+'.lean');snap.write_bytes(src.read_bytes());obj=dst/(n+'.olean');cmd=[str(lean),'-M6000','-j1','-DElab.async=false',str(src),'-o',str(obj)];t=time.monotonic();p=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log=logs/(n+'.log');log.write_text(p.stdout);row={'module':n,'exit':p.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(src),'object_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log),'command':cmd};state['records'].append(row);save();print(n,p.returncode,round(row['seconds'],1),flush=True)
  if p.returncode or re.search(r'(?m)^.*error:|\bsorryAx\b',p.stdout):raise RuntimeError('compile failed: '+n+'\n'+p.stdout)
  if n.endswith('Checks'):
   groups=re.findall(r'depends on axioms:\s*\[([^]]*)\]',p.stdout,re.S)
   if len(re.findall(r'depends on axioms:|does not depend on any axioms', p.stdout))!=8 or any({x.strip() for x in g.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for g in groups):raise RuntimeError('unexpected axiom checks')
  must(src,baseline['sources'][n],'source after')
 state.update(phase='final authentication',module=None);save()
 for f,h in baseline['selected_parent_objects'].items():must(PARENT/f,h,'final parent')
 for n,h in baseline['sources'].items():must(SOURCE/(n+'.lean'),h,'final source')
 for f,h in baseline['direct_source_observations'].items():must(ROOT/f,h,'final observed source')
 must(lean,baseline['lean_sha256'],'final compiler')
 for row in state['records']:
  n=row['module'];must(dst/(n+'.olean'),row['object_sha256'],'output');must(logs/(n+'.log'),row['log_sha256'],'log')
 state.update(status='PASS',phase='complete');save();print('PASS',root,flush=True)
except BaseException as exc:
 state.update(status='FAILED',failure={'type':type(exc).__name__,'message':str(exc),'phase':state.get('phase'),'module':state.get('module')});save();print('FAILED',root,state['failure'],flush=True);raise
