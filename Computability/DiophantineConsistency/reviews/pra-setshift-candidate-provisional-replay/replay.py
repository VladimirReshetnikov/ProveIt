#!/usr/bin/env python3
"""Replay a conditional setShift graph bound on an unauthenticated parent.

The current declared project import closure is hash-guarded. Inherited object
hashes are not certificates that those objects match the current sources.
Foundation, ZFCinPA and package object provenance is inherited.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,tempfile,time
ROOT=Path(__file__).resolve().parents[4]
SRC=ROOT/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
PARENT=Path('/tmp/pra-setshift-coherent/lib')
PACKET=Path(__file__).resolve().parent
M=json.loads((PACKET/'manifest.json').read_text())
sha=lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
targets=['PRAWitnessSetShiftCandidate','PRAWitnessSetShiftCandidateChecks']
work=Path(tempfile.mkdtemp(prefix='pra-setshift-candidate-independent-'))
lib=work/'lib'; dest=lib/'DiophantineConsistency'; dest.mkdir(parents=True)
logs=work/'logs';logs.mkdir()
for name in ['Foundation','ZFCinPA']:
 (lib/name).symlink_to((PARENT/name).resolve(),target_is_directory=True)
for f in (PARENT/'DiophantineConsistency').glob('*.olean'):
 if f.stem not in targets:(dest/f.name).symlink_to(f.resolve())
base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip()
env=dict(os.environ,LEAN_PATH=str(lib)+':'+base,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
state={'status':'RUNNING','root':str(work),'parent':str(PARENT),'manifest_sha256':sha(PACKET/'manifest.json'),
       'records':[], 'scope':M['scope']}
def save():
 (work/'state.tmp').write_text(json.dumps(state,indent=2)+'\n');(work/'state.tmp').replace(work/'state.json')
def audit():
 assert all(sha(SRC/(n+'.lean'))==h for n,h in M['project_sources'].items())
 assert all(sha(dest/(n+'.olean'))==h for n,h in M['inherited_project_objects'].items())
 assert sha(lib/'ZFCinPA/Instances.olean')==M['zfc_instances_olean_sha256']
 assert sha(PACKET/'manifest.json')==state['manifest_sha256']
save(); print('ROOT',work,'guarded',len(M['inherited_project_objects']),'inherited project objects',flush=True)
try:
 audit()
 for n in targets:
  state['module']=n;save(); log=logs/(n+'.log');obj=dest/(n+'.olean');start=time.monotonic()
  with log.open('w') as f:
   p=subprocess.run(['lean','-M6000','-j1','-DElab.async=false','--root='+str(SRC.parent),str(SRC/(n+'.lean')),'-o',str(obj)],cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
  row={'module':n,'exit':p.returncode,'seconds':time.monotonic()-start,'source_sha256':sha(SRC/(n+'.lean')),'object_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log)};state['records'].append(row);save()
  assert p.returncode==0 and not re.search(r'\b(?:warning|error|sorryAx)\b',log.read_text())
  print('PASS',n,flush=True)
 audit();state.update(status='PASS',module=None);save();print('PASS',work,flush=True)
except BaseException as exc:
 state.update(status='FAILED',failure=repr(exc));save();raise
