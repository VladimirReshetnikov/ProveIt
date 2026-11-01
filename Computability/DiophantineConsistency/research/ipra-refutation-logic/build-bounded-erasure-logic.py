"""Scoped replay of intuitionistic bounded-erasure logical steps.

The five Foundation source/object pairs are hashed as inherited anchors; no
claim is made that those objects were built from those source files or that
their transitive closure is source-current.
"""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path(__file__).resolve().parents[4]
SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
F=Path('/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation')
O=Path('/home/codex/src/Proofs/.lake/build/lib/lean')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
names=['IPRABoundedErasureLogic','IPRABoundedErasureLogicChecks']
anchors=['Foundation/FirstOrder/NegationTranslation/GoedelGentzen','Foundation/FirstOrder/Intuitionistic/Deduction','Foundation/FirstOrder/Intuitionistic/Rew','Foundation/FirstOrder/Intuitionistic/Formula','Foundation/Meta/IntProver']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
sourceh={n:sha(SRC/(n+'.lean')) for n in names}
anch={x:{'source':sha(F/(x+'.lean')),'object':sha(O/(x+'.olean'))} for x in anchors}
leanh=sha(LEAN)
w=Path(tempfile.mkdtemp(prefix='ipra-bounded-erasure-logic-'));lib=w/'lib';lib.mkdir();(lib/'DiophantineConsistency').mkdir();(w/'logs').mkdir();(w/'src/DiophantineConsistency').mkdir(parents=True)
shutil.copyfile(__file__,w/'driver.py')
for n in names:
 shutil.copyfile(SRC/(n+'.lean'),w/'src/DiophantineConsistency'/(n+'.lean'))
 shutil.copyfile(SRC/(n+'.lean'),w/'logs'/(n+'.lean'))
base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=R,text=True).strip()
paths=[str(lib),'/tmp/pahf-calculus-simp-217',str(O),*base.split(':')]
for x in anchors:
 selected=next((Path(d)/(x+'.olean') for d in paths if (Path(d)/(x+'.olean')).is_file()),None)
 assert selected is not None and selected.resolve()==(O/(x+'.olean')).resolve(),(x,selected)
state={'status':'RUNNING','private':str(w),'source_sha256':sourceh,'foundation_anchors':anch,'lean_sha256':leanh,'lean_path':paths[1:],'scope':'Intuitionistic Hilbert proof combinators for erasure under conjunction, native disjunction, universal and guarded existential. No bnd-recursion binding, iPRA theory or full Foundation/package source-current provenance asserted.'}
def save(): (w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def auth():
 return sha(LEAN)==leanh and all(sha(SRC/(n+'.lean'))==sourceh[n] and sha(w/'src/DiophantineConsistency'/(n+'.lean'))==sourceh[n] and sha(w/'logs'/(n+'.lean'))==sourceh[n] for n in names) and all(sha(F/(x+'.lean'))==a['source'] and sha(O/(x+'.olean'))==a['object'] for x,a in anch.items())
save();print('PRIVATE',w,flush=True)
try:
 assert auth();env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['records']=[]
 for n in names:
  out=lib/'DiophantineConsistency'/(n+'.olean');cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10',str(LEAN),'--root='+str(w/'src'),'-M6000','-j1','-DElab.async=false','-o',str(out),str(w/'src/DiophantineConsistency'/(n+'.lean'))];t=time.monotonic()
  with (w/'logs'/(n+'.log')).open('w') as log:
   code=subprocess.run(['/usr/bin/time','-v','-o',str(w/'logs'/(n+'.time')),*cmd],cwd=R,env=env,stdout=log,stderr=subprocess.STDOUT).returncode
  state['records'].append(dict(name=n,exit=code,object_sha256=sha(out) if out.exists() else None,log_sha256=sha(w/'logs'/(n+'.log')),seconds=time.monotonic()-t));save();print(n,code,flush=True);assert code==0
 assert auth();state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();raise
