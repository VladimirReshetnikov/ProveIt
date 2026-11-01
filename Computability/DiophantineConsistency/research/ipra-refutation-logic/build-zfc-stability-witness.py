"""Scoped replay of intuitionistic syntactic erasure of all bnd guards.

The inherited ZFC/HA, Foundation and package closure is not rebuilt or
source/object authenticated. We pin the exact selected parents, direct objects,
source snapshots, logs and Foundation anchors before and after compilation.
"""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path(__file__).resolve().parents[4]; SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
F=Path('/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation');O=Path('/home/codex/src/Proofs/.lake/build/lib/lean');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
Q=Path('/tmp/ipra-zfc-theory-stability-tdaxlo6u');I=Path('/tmp/ipra-theory-instantiation-k2lctg6h');U=Path('/tmp/ipra-zfc-reach-stability-a_ph_32d');J=Path('/tmp/ipra-theory-hilbert-bridge-rw4z4_1w');Y=Path('/tmp/ipra-stable-backward-reach-n8l0047w');V=Path('/tmp/ipra-zfc-matrix-comparison-5mjjos6j');S=Path('/tmp/ipra-stable-backward-gqjj3ia_');Z=Path('/tmp/ipra-zfc-mapped-erasure-t5536x4m');X=Path('/tmp/ipra-existential-comparison-akagnpdq');M=Path('/tmp/ipra-bounded-mapped-erasure-xo_wodgx');B=Path('/tmp/ipra-bounded-erasure-bf7m6b7p');W=Path('/tmp/ipra-zfc-witness-bound-_ar520xu');E=Path('/tmp/ipra-bounded-erasure-logic-logxg8r1');N=Path('/tmp/ipra-native-forward-77hc1klz');package=Path('/tmp/ha87-full-source-jrvxi6bb/package-lib')
read=lambda p:json.loads(Path(p).read_text());sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
qs,ins,us,js,ys,vs,ss,zs,xs,ms,bs,ws,es,ns=[read(p/'state.json') for p in [Q,I,U,J,Y,V,S,Z,X,M,B,W,E,N]];assert all(s['status']=='PASS' for s in [qs,ins,us,js,ys,vs,ss,zs,xs,ms,bs,ws,es,ns]);assert package.is_dir()
parents={str(p):sha(p/'state.json') for p in [Q,I,U,J,Y,V,S,Z,X,M,B,W,E,N]};anch=ws['foundation_anchors'];assert anch==es['foundation_anchors']==ns['foundation_anchors'];leanh=sha(LEAN)
names=['IPRAFoundationZFCStabilityWitness','IPRAFoundationZFCStabilityWitnessChecks'];sourceh={n:sha(SRC/(n+'.lean')) for n in names}
direct=[(Q,qs,'IPRAFoundationZFCTheoryStability'),(I,ins,'IPRATheoryInstantiation'),(U,us,'IPRAFoundationZFCReachStability'),(J,js,'IPRATheoryHilbertBridge'),(Y,ys,'IPRAStableBackwardReach'),(V,vs,'IPRAFoundationZFCMatrixComparison'),(S,ss,'IPRAStableBackward'),(Z,zs,'IPRAFoundationZFCMappedErasure'),(X,xs,'IPRAExistentialComparison'),(M,ms,'IPRABoundedMappedErasure'),(W,ws,'IPRAFoundationZFCWitnessBound'),(B,bs,'IPRABoundedErasure'),(W,ws,'StrictSigmaOneInduction'),(E,es,'IPRABoundedErasureLogic'),(N,ns,'IPRANativeFormulaRew')]
selected={n:next(x for x in st['records'] if x['name']==n) for _,st,n in direct}
w=Path(tempfile.mkdtemp(prefix='ipra-zfc-stability-witness-'));lib=w/'lib';lib.mkdir();(w/'logs').mkdir();(w/'src/DiophantineConsistency').mkdir(parents=True);shutil.copyfile(__file__,w/'driver.py')
for n in names:shutil.copyfile(SRC/(n+'.lean'),w/'src/DiophantineConsistency'/(n+'.lean'));shutil.copyfile(SRC/(n+'.lean'),w/'logs'/(n+'.lean'))
for top in (Q/'lib').iterdir():
 if top.name!='DiophantineConsistency':(lib/top.name).symlink_to(top.resolve(),target_is_directory=top.is_dir());continue
 for root,dirs,files in os.walk(top,followlinks=True):
  for f in files:
   path=Path(root)/f;dest=lib/path.relative_to(Q/'lib');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(path.resolve())
out=lib/'DiophantineConsistency/IPRATheoryInstantiation.olean';assert not out.exists();out.symlink_to((I/'lib/DiophantineConsistency/IPRATheoryInstantiation.olean').resolve())
for parent,st,n in direct:assert (lib/'DiophantineConsistency'/(n+'.olean')).resolve()==(parent/'lib/DiophantineConsistency'/(n+'.olean')).resolve()
state={'status':'RUNNING','private':str(w),'parents':parents,'source_sha256':sourceh,'direct_records':selected,'foundation_anchors':anch,'lean_sha256':leanh,'scope':'Exact mapped Foundation ZFC consistency equivalence follows conditionally from a translated witness-bound T-proof and T-proofs of explicitly represented finite-parameter stability schemas for each reachable relevant bounded-matrix formula. Each witness includes its arity, closed-binder formula, term vector, theory proof and exact instance equality. No such arithmetic proofs or witnesses are constructed. No arithmetic axioms, bounded decidability, or semantic model proof is used. No bounded matrix comparison, standard iPRA identification, or PAHF/native correspondence is established. Inherited Foundation and package transitive source/object ancestry is not authenticated.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def auth():
 if sha(LEAN)!=leanh or not all(sha(Path(x)/'state.json')==v for x,v in parents.items()):return False
 if not all(sha(SRC/(n+'.lean'))==h and sha(w/'src/DiophantineConsistency'/(n+'.lean'))==h and sha(w/'logs'/(n+'.lean'))==h for n,h in sourceh.items()):return False
 if not all(sha(F/(x+'.lean'))==v['source'] and sha(O/(x+'.olean'))==v['object'] and sha(W/'lib'/(x+'.olean'))==v['object'] for x,v in anch.items()):return False
 for p,st,n in direct:
  x=selected[n]
  if sha(SRC/(n+'.lean'))!=st['source_sha256'][n] or sha(p/'lib/DiophantineConsistency'/(n+'.olean'))!=x['object_sha256'] or sha(p/'logs'/(n+'.log'))!=x['log_sha256'] or sha(lib/'DiophantineConsistency'/(n+'.olean'))!=x['object_sha256']:return False
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
