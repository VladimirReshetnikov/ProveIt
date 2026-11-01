"""Guarded sub-self replay, with explicitly historical hbound provider boundary."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path(__file__).resolve().parents[4];SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
F=Path('/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation');O=Path('/home/codex/src/Proofs/.lake/build/lib/lean');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
B=Path('/tmp/ipra-induction-nozero-nra7kfs5');J=Path('/tmp/ipra-theory-hilbert-bridge-rw4z4_1w');I=Path('/tmp/ipra-theory-instantiation-k2lctg6h');package=Path('/tmp/ha87-full-source-jrvxi6bb/package-lib')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());bs,js,ins=[read(p/'state.json') for p in (B,J,I)];assert all(s['status']=='PASS' for s in (bs,js,ins));parents={str(p):sha(p/'state.json') for p in (B,J,I)};anchors=js['foundation_anchors'];assert anchors==ins['foundation_anchors'];leanh=sha(LEAN)
names=['IPRANativeSubSelf','IPRANativeSubSelfChecks'];sourceh={n:sha(SRC/(n+'.lean')) for n in names};sources=['PRAEqualityCode','IPRAFullGGTransfer'];sourceanchors={n:sha(SRC/(n+'.lean')) for n in sources}
selected={}
for top in (B/'lib').iterdir():
 if top.name not in ('DiophantineConsistency','Foundation','ZFCinPA'):continue
 for base,dirs,files in os.walk(top,followlinks=True):
  for f in files:
   if '.olean' in f or f.endswith('.ir'):
    p=Path(base)/f;selected[str(p.relative_to(B/'lib'))]={'path':str(p.resolve()),'sha256':sha(p)}
for n in sources:assert 'DiophantineConsistency/'+n+'.olean' in selected
w=Path(tempfile.mkdtemp(prefix='ipra-native-subself-v3-'));lib=w/'lib';lib.mkdir();(w/'src/DiophantineConsistency').mkdir(parents=True);(w/'logs').mkdir();shutil.copyfile(__file__,w/'driver.py')
for n in names:
 shutil.copyfile(SRC/(n+'.lean'),w/'src/DiophantineConsistency'/(n+'.lean'));shutil.copyfile(SRC/(n+'.lean'),w/'logs'/(n+'.lean'))
for rel,v in selected.items():
 out=lib/rel;out.parent.mkdir(parents=True,exist_ok=True);out.symlink_to(v['path'])
for p,st,n in [(J,js,'IPRATheoryHilbertBridge'),(I,ins,'IPRATheoryInstantiation')]:
 out=lib/'DiophantineConsistency'/(n+'.olean');assert not out.exists();out.symlink_to((p/'lib/DiophantineConsistency'/(n+'.olean')).resolve())
for n,v in anchors.items():assert sha(B/'lib'/(n+'.olean'))==v['object']
(w/'providers.json').write_text(json.dumps(selected,indent=2,sort_keys=True)+'\n');inventoryh=sha(w/'providers.json')
state={'status':'RUNNING','private':str(w),'parents':parents,'source_sha256':sourceh,'historical_direct_source_anchors':sourceanchors,'foundation_anchors':anchors,'lean_sha256':leanh,'provider_inventory_sha256':inventoryh,'provider_objects':len(selected),'scope':'Positive native sub-self equality from an explicit native zero-decidability proof, via a classical PRA model-completeness proof, full GG transfer and intuitionistic elimination of double negation using zero decidability. No zero-decidability proof or two-difference correctness theorem is supplied. Parent project and package source/object transitive provenance remain historical; source anchors are not claimed to build inherited objects.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def auth():
 if sha(LEAN)!=leanh or sha(w/'providers.json')!=inventoryh or not all(sha(Path(p)/'state.json')==h for p,h in parents.items()):return False
 if not all(sha(SRC/(n+'.lean'))==h and sha(w/'src/DiophantineConsistency'/(n+'.lean'))==h and sha(w/'logs'/(n+'.lean'))==h for n,h in sourceh.items()):return False
 if not all(sha(SRC/(n+'.lean'))==h for n,h in sourceanchors.items()):return False
 if not all(sha(x['path'])==x['sha256'] and sha(lib/k)==x['sha256'] for k,x in selected.items()):return False
 if not all(sha(F/(x+'.lean'))==v['source'] and sha(O/(x+'.olean'))==v['object'] and sha(B/'lib'/(x+'.olean'))==v['object'] for x,v in anchors.items()):return False
 for p,st,n in [(J,js,'IPRATheoryHilbertBridge'),(I,ins,'IPRATheoryInstantiation')]:
  row=next(x for x in st['records'] if x['name']==n)
  if sha(SRC/(n+'.lean'))!=st['source_sha256'][n] or sha(p/'lib/DiophantineConsistency'/(n+'.olean'))!=row['object_sha256'] or sha(p/'logs'/(n+'.log'))!=row['log_sha256'] or sha(lib/'DiophantineConsistency'/(n+'.olean'))!=row['object_sha256']:return False
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
