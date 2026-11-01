"""Narrow scoped replay of the exact Foundation bounded-refutation specialization.

Pins the direct ZFC definition objects, pure logic providers and five external
Foundation anchors. It does not rehash the full inherited HA/package closure
and does not assert source/object correspondence for inherited objects.
"""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path(__file__).resolve().parents[4];SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
F=Path('/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation');O=Path('/home/codex/src/Proofs/.lake/build/lib/lean');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
H=Path('/tmp/ha87-focused-validator-rebase-q6geuvc7');P=Path('/tmp/ipra-refutation-logic-szcjealp');Q=Path('/tmp/ipra-refutation-theory-zc6qqhz7');N=Path('/tmp/ipra-native-forward-77hc1klz');package=Path('/tmp/ha87-full-source-jrvxi6bb/package-lib')
read=lambda p:json.loads(Path(p).read_text());sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
Z=Path('/tmp/ipra-zfc-one-premise-ufvdpy0w');M=Path('/tmp/ipra-zfc-mapped-4otiigqv');W=Path('/tmp/ipra-witness-bridge-_2dmsm0w');hs,ps,qs,ns,zs,ms,ws=[read(x/'state.json') for x in [H,P,Q,N,Z,M,W]];assert all(x['status']=='PASS' for x in [hs,ps,qs,ns,zs,ms,ws]);assert package.is_dir()
parents={str(x):sha(x/'state.json') for x in [H,P,Q,N,Z,M,W]};anch=ps['foundation_anchors'];assert anch==qs['foundation_anchors']==ns['foundation_anchors'];leanh=sha(LEAN)
names=['StrictSigmaOneInduction','IPRAFoundationZFCWitnessBound','IPRAFoundationZFCWitnessBoundChecks'];sourceh={n:sha(SRC/(n+'.lean')) for n in names}
zfcnames=['FoundationHAConsistencyNormalization','FoundationZFCConsistencyNat'];zfcanchors={n:{'source':sha(SRC/(n+'.lean')),'object':sha(H/'lib/DiophantineConsistency'/(n+'.olean'))} for n in zfcnames}
for n,v in zfcanchors.items():assert hs['historical_boundary_objects']['DiophantineConsistency/'+n+'.olean']==v['object']
w=Path(tempfile.mkdtemp(prefix='ipra-zfc-witness-bound-'));lib=w/'lib';lib.mkdir();(w/'logs').mkdir();(w/'src/DiophantineConsistency').mkdir(parents=True);shutil.copyfile(__file__,w/'driver.py')
for n in names:
 shutil.copyfile(SRC/(n+'.lean'),w/'src/DiophantineConsistency'/(n+'.lean'));shutil.copyfile(SRC/(n+'.lean'),w/'logs'/(n+'.lean'))
for top in (M/'lib').iterdir():
 if top.name!='DiophantineConsistency':(lib/top.name).symlink_to(top.resolve(),target_is_directory=top.is_dir());continue
 for root,dirs,files in os.walk(top,followlinks=True):
  for f in files:
   path=Path(root)/f;dest=lib/path.relative_to(M/'lib');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(path.resolve())
out=lib/'DiophantineConsistency/IPRARefutationWitnessBridge.olean';assert not out.exists();out.symlink_to((W/'lib/DiophantineConsistency/IPRARefutationWitnessBridge.olean').resolve())
state={'status':'RUNNING','private':str(w),'parents':parents,'source_sha256':sourceh,'zfc_direct_anchors':zfcanchors,'foundation_anchors':anch,'lean_sha256':leanh,'scope':'Exact mapped Foundation ZFC GG consistency and literal ∃b,bnd rho; syntactic Σ₀ matrix certificate plus three explicit unproved theory-proof premises. No iPRA instance, backward proof, PAHF/native identification, or complete HA/Foundation/package source/object closure is asserted. Only direct ZFC objects and selected external anchors are rehashed.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def auth():
 if sha(LEAN)!=leanh or not all(sha(Path(x)/'state.json')==v for x,v in parents.items()):return False
 if not all(sha(SRC/(n+'.lean'))==h and sha(w/'src/DiophantineConsistency'/(n+'.lean'))==h and sha(w/'logs'/(n+'.lean'))==h for n,h in sourceh.items()):return False
 if not all(sha(SRC/(n+'.lean'))==v['source'] and sha(H/'lib/DiophantineConsistency'/(n+'.olean'))==v['object'] for n,v in zfcanchors.items()):return False
 if not all(sha(F/(x+'.lean'))==v['source'] and sha(O/(x+'.olean'))==v['object'] and sha(H/'lib'/(x+'.olean'))==v['object'] for x,v in anch.items()):return False
 for parent,st in [(P,ps),(Q,qs),(N,ns),(Z,zs),(M,ms),(W,ws)]:
  if not all(sha(SRC/(x['name']+'.lean'))==st['source_sha256'][x['name']] and sha(parent/'lib/DiophantineConsistency'/(x['name']+'.olean'))==x['object_sha256'] and sha(parent/'logs'/(x['name']+'.log'))==x['log_sha256'] for x in st['records']):return False
 return True
save();print('PRIVATE',w,flush=True)
try:
 assert auth();env=dict(os.environ,LEAN_PATH=':'.join([str(lib),str(package)]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['records']=[]
 for n in names:
  out=lib/'DiophantineConsistency'/(n+'.olean');assert not out.exists();cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10',str(LEAN),'--root='+str(w/'src'),'-M8000','-j1','-DElab.async=false','-o',str(out),str(w/'src/DiophantineConsistency'/(n+'.lean'))];t=time.monotonic()
  with (w/'logs'/(n+'.log')).open('w') as log:code=subprocess.run(['/usr/bin/time','-v','-o',str(w/'logs'/(n+'.time')),*cmd],cwd=R,env=env,stdout=log,stderr=subprocess.STDOUT).returncode
  state['records'].append(dict(name=n,exit=code,object_sha256=sha(out) if out.exists() else None,log_sha256=sha(w/'logs'/(n+'.log')),seconds=time.monotonic()-t));save();print(n,code,flush=True);assert code==0
 assert auth();state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=repr(e));save();raise
