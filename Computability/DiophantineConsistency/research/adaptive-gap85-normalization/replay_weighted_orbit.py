#!/usr/bin/env python3
"""Guarded replay of weighted orbit code and normalized-coordinate uniqueness."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
SRC=R/'Computability/DiophantineConsistency/research/adaptive-gap85-normalization'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
provider=Path('/tmp/gap85-actual-joint-replay-4ijot54j')
boundary=[Path(p) for p in json.load(open(provider/'state.json'))['boundary']]
names=['AdaptiveGap85WeightedOrbit']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
objects=sorted(p for p in (provider/'lib/DiophantineConsistency').glob('*.olean*') if p.is_file())
assert json.load(open(provider/'state.json'))['status']=='PASS'
parent=json.load(open(provider/'state.json'))
family=provider/'lib/DiophantineConsistency/AdaptiveGap85ActualJoint.olean'
family_source=provider/'src/DiophantineConsistency/AdaptiveGap85ActualJoint.lean'
family_record=next(row for row in parent['records'] if row['module']=='AdaptiveGap85ActualJoint')
assert sha(family)==family_record['object_sha256'] and sha(family_source)==family_record['source_sha256']
external=provider/'lib/Foundation/FirstOrder/Arithmetic/HFS/PRF.olean'
assert external.is_file()
files=[Path(__file__).resolve(),LEAN,provider/'state.json',family,family_source,external,*[SRC/(n+'.lean') for n in names],*objects]
anchors={str(p):sha(p) for p in files}
w=Path(tempfile.mkdtemp(prefix='gap85-weighted-orbit-replay-'));src=w/'src';lib=w/'lib';logs=w/'logs'
for p in [src/'DiophantineConsistency',lib/'DiophantineConsistency',logs]:p.mkdir(parents=True,exist_ok=True)
for p in (provider/'lib').iterdir():
 if p.name!='DiophantineConsistency': (lib/p.name).symlink_to(p, target_is_directory=p.is_dir())
for p in (provider/'lib/DiophantineConsistency').iterdir():
 if not any(p.name.startswith(n+'.') for n in names): (lib/'DiophantineConsistency'/p.name).symlink_to(p, target_is_directory=p.is_dir())
for n in names:shutil.copyfile(SRC/(n+'.lean'),src/'DiophantineConsistency'/(n+'.lean'))
(src/'DiophantineConsistency/AdaptiveGap85WeightedOrbitChecks.lean').write_text('import DiophantineConsistency.AdaptiveGap85WeightedOrbit\n#print axioms DiophantineConsistency.AdaptiveGap85WeightedOrbit.orbit_gap_code\n#print axioms DiophantineConsistency.AdaptiveGap85WeightedOrbit.orbit_unique_gap_pair\n#print axioms DiophantineConsistency.AdaptiveGap85WeightedOrbit.orbit_large_remainder_blocks\n#check DiophantineConsistency.AdaptiveGap85WeightedOrbit.orbit_gap_code\n#check DiophantineConsistency.AdaptiveGap85WeightedOrbit.orbit_unique_gap_pair\n#check DiophantineConsistency.AdaptiveGap85WeightedOrbit.orbit_large_remainder_blocks\n')
env=dict(os.environ,LEAN_PATH=':'.join(map(str,[lib,*boundary])),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
s={'status':'RUNNING','root':str(w),'provider':str(provider),'parent_project_object_count':len(objects),'anchors':anchors,'boundary':list(map(str,boundary)),'records':[],'scope':'In every IΣ₁ model, any reverse-gap endpoint of the specified external finite three-shift orbit has qF+C equal to the initial qF+C remainder modulo cU, so its F,C coordinates are unique. A remainder at least q² conditionally rules out such an endpoint. Neither occurrence at a full zero nor a reachable endpoint is asserted; the reverse implication remains open. Selected inherited project objects pinned; original transitive project/package source ancestry historical.'}
def save():(w/'state.json').write_text(json.dumps(s,indent=2)+'\n')
def audit():
 for p,h in anchors.items():
  if not Path(p).is_file() or sha(p)!=h:raise RuntimeError('guard changed: '+p)
 for n in names:
  if sha(src/'DiophantineConsistency'/(n+'.lean'))!=anchors[str(SRC/(n+'.lean'))]:raise RuntimeError('source snapshot changed '+n)
save();print('ROOT',w,'PARENT_OBJECTS',len(objects),flush=True)
try:
 audit()
 for name in [*names,'AdaptiveGap85WeightedOrbitChecks']:
  f=src/'DiophantineConsistency'/(name+'.lean');o=lib/'DiophantineConsistency'/(name+'.olean');l=logs/(name+'.log')
  with l.open('w') as out:r=subprocess.run([str(LEAN),'-M6000','-j1','-DElab.async=false','--root='+str(src),str(f),'-o',str(o)],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
  content=l.read_text();s['records'].append({'module':name,'exit':r.returncode,'source_sha256':sha(f),'object_sha256':sha(o) if o.exists() else None,'log_sha256':sha(l),'warnings':content.count('warning:')});save()
  if r.returncode or 'sorryAx' in content or 'error:' in content or 'warning:' in content:raise RuntimeError('compile failed '+name+': '+content)
  if name.endswith('Checks'):
   axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',content,re.S)
   if len(axioms)!=3 or any({a.strip() for a in x.split(',') if a.strip()}-{'propext','Classical.choice','Quot.sound'} for x in axioms):raise RuntimeError('unexpected axiom report')
 audit()
 for row in s['records']:
  if sha(lib/'DiophantineConsistency'/(row['module']+'.olean'))!=row['object_sha256'] or sha(logs/(row['module']+'.log'))!=row['log_sha256']:raise RuntimeError('output changed')
 s['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:
 s.update(status='FAILED',failure=str(e));save();print('FAILED',str(e),flush=True);raise
