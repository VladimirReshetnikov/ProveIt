"""Narrow scoped replay of candidate iPRA exact-ZFC specialization.

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
V=Path('/tmp/ipra-zfc-finite-stability-fe_5xavk');Z=Path('/tmp/ipra-zfc-one-premise-ufvdpy0w');M=Path('/tmp/ipra-zfc-mapped-4otiigqv');C=Path('/tmp/ipra-induction-nozero-k3g0sdt4');manifest=R/'Computability/DiophantineConsistency/reviews/ipra-native-theory-replay/manifest.json';cm=read(manifest);cmh=sha(manifest);vs,hs,ps,qs,ns,zs,ms,cs=[read(x/'state.json') for x in [V,H,P,Q,N,Z,M,C]];assert all(x['status']=='PASS' for x in [vs,hs,ps,qs,ns,zs,ms,cs]);assert package.is_dir()
parents={str(x):sha(x/'state.json') for x in [V,H,P,Q,N,Z,M,C]};anch=ps['foundation_anchors'];assert anch==qs['foundation_anchors']==ns['foundation_anchors'];leanh=sha(LEAN)
names=['IPRAFoundationZFCCandidateFiniteStability','IPRAFoundationZFCCandidateFiniteStabilityChecks'];sourceh={n:sha(SRC/(n+'.lean')) for n in names}
zfcnames=['FoundationHAConsistencyNormalization','FoundationZFCConsistencyNat'];zfcanchors={n:{'source':sha(SRC/(n+'.lean')),'object':sha(H/'lib/DiophantineConsistency'/(n+'.olean'))} for n in zfcnames}
for n,v in zfcanchors.items():assert hs['historical_boundary_objects']['DiophantineConsistency/'+n+'.olean']==v['object']
w=Path(tempfile.mkdtemp(prefix='ipra-zfc-candidate-finite-stability-'));lib=w/'lib';lib.mkdir();(w/'logs').mkdir();(w/'src/DiophantineConsistency').mkdir(parents=True);shutil.copyfile(__file__,w/'driver.py')
for n in names:
 shutil.copyfile(SRC/(n+'.lean'),w/'src/DiophantineConsistency'/(n+'.lean'));shutil.copyfile(SRC/(n+'.lean'),w/'logs'/(n+'.lean'))
for top in (V/'lib').iterdir():
 if top.name!='DiophantineConsistency':(lib/top.name).symlink_to(top.resolve(),target_is_directory=top.is_dir());continue
 for root,dirs,files in os.walk(top,followlinks=True):
  for f in files:
   path=Path(root)/f;dest=lib/path.relative_to(V/'lib');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(path.resolve())
native_names=['IPRANativeTheory','IPRANativeInduction','IPRAQuantifierFree','PRATheory','PRALanguage','PRACodeEncoding','PRAFiniteFunctionCodes','PRAFunctionCodes']
for n in native_names:
 out=lib/'DiophantineConsistency'/(n+'.olean');assert not out.exists();out.symlink_to((C/'lib/DiophantineConsistency'/(n+'.olean')).resolve())
external_names=['Foundation/FirstOrder/Arithmetic/Basic/Model.olean','Foundation/FirstOrder/Arithmetic/Schemata.olean','Foundation/FirstOrder/NegationTranslation/GoedelGentzen.olean']
assert all(sha(C/'lib'/x)==sha(M/'lib'/x) for x in external_names)
mathlib=Path('/home/codex/src/Proofs/.lake/packages/mathlib/.lake/build/lib/lean');external_math=['Mathlib/Computability/Primrec/List.olean','Mathlib/Data/Nat/Pairing.olean'];assert all(sha(mathlib/x)==sha(package/x) for x in external_math)
native_theory=next(x for x in cs['records'] if x['module']=='IPRANativeTheory')
native_anchors={n:{'source':native_theory['source_sha256'] if n=='IPRANativeTheory' else cm['workspace_sources'][str((SRC/(n+'.lean')).relative_to(R))],'object':native_theory['object_sha256'] if n=='IPRANativeTheory' else cm['parent_objects'][n]} for n in native_names}
external_anchors={n:sha(M/'lib'/n) for n in external_names};math_anchors={n:sha(package/n) for n in external_math}
state={'native_manifest_sha256':cmh,'native_anchors':native_anchors,'external_anchors':external_anchors,'mathlib_anchors':math_anchors,'status':'RUNNING','private':str(w),'parents':parents,'source_sha256':sourceh,'zfc_direct_anchors':zfcanchors,'foundation_anchors':anch,'lean_sha256':leanh,'scope':'Exact Foundation ZFC consistency equivalence in candidate native theory conditional on a translated witness-bound proof and explicit finite-parameter nativeTheory stability-schema witnesses for relevant formulas in a computable finite list covering the opened bounded matrix. No evaluated literal list/count, stability-schema or witness-bound proof, standard-iPRA identification, axiom-image, PAHF/native identification, or complete HA/Foundation/package source/object closure is asserted. Only direct ZFC objects and selected external anchors are rehashed.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def auth():
 if sha(manifest)!=cmh or not all(sha(SRC/(n+'.lean'))==a['source'] and sha(C/'lib/DiophantineConsistency'/(n+'.olean'))==a['object'] for n,a in native_anchors.items()) or not all(sha(C/'lib'/n)==v and sha(M/'lib'/n)==v for n,v in external_anchors.items()) or not all(sha(mathlib/n)==v and sha(package/n)==v for n,v in math_anchors.items()):return False
 if sha(LEAN)!=leanh or not all(sha(Path(x)/'state.json')==v for x,v in parents.items()):return False
 if not all(sha(SRC/(n+'.lean'))==h and sha(w/'src/DiophantineConsistency'/(n+'.lean'))==h and sha(w/'logs'/(n+'.lean'))==h for n,h in sourceh.items()):return False
 if not all(sha(SRC/(n+'.lean'))==v['source'] and sha(H/'lib/DiophantineConsistency'/(n+'.olean'))==v['object'] for n,v in zfcanchors.items()):return False
 if not all(sha(F/(x+'.lean'))==v['source'] and sha(O/(x+'.olean'))==v['object'] and sha(H/'lib'/(x+'.olean'))==v['object'] for x,v in anch.items()):return False
 for parent,st in [(V,vs),(P,ps),(Q,qs),(N,ns),(Z,zs),(M,ms)]:
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
