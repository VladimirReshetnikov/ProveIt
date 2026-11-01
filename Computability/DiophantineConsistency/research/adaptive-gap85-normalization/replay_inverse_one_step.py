#!/usr/bin/env python3
"""Replay the coherent inverse-one-step criterion and 85-to-86 client."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
SRC=R/'Computability/DiophantineConsistency/research/adaptive-gap85-normalization'
LEAN_SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
provider=Path('/tmp/gap85-inverse-old-replay-3q58x85q')
parent=json.load(open(provider/'state.json'))
assert parent['status']=='PASS'
boundary=[Path(p) for p in parent['boundary']]
names=['AdaptiveGap85BalanceNoCross','AdaptiveGap85ForwardOrbitNoCross','AdaptiveGap85InverseEntry','AdaptiveGap85InverseOneStep']
sources=[SRC/(n+'.lean') for n in names]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
objects=sorted(p for p in (provider/'lib/DiophantineConsistency').glob('*.olean*') if p.is_file())
parent_output=provider/'lib/DiophantineConsistency/AdaptiveGap85InverseOld.olean'
parent_source=provider/'src/DiophantineConsistency/AdaptiveGap85InverseOld.lean'
record=next(row for row in parent['records'] if row['module']=='AdaptiveGap85InverseOld')
assert sha(parent_output)==record['object_sha256'] and sha(parent_source)==record['source_sha256']
external=provider/'lib/Foundation/FirstOrder/Arithmetic/HFS/PRF.olean'
assert external.is_file()
files=[Path(__file__).resolve(),LEAN,provider/'state.json',parent_output,parent_source,external,*sources,*objects]
anchors={str(p):sha(p) for p in files}
w=Path(tempfile.mkdtemp(prefix='gap85-inverse-one-step-replay-'));src=w/'src';lib=w/'lib';logs=w/'logs'
for p in [src/'DiophantineConsistency',lib/'DiophantineConsistency',logs]:p.mkdir(parents=True,exist_ok=True)
for p in (provider/'lib').iterdir():
 if p.name!='DiophantineConsistency':(lib/p.name).symlink_to(p,target_is_directory=p.is_dir())
for p in (provider/'lib/DiophantineConsistency').iterdir():
 if not any(p.name.startswith(n+'.') for n in names):(lib/'DiophantineConsistency'/p.name).symlink_to(p,target_is_directory=p.is_dir())
for name,f in zip(names,sources):shutil.copyfile(f,src/'DiophantineConsistency'/(name+'.lean'))
(src/'DiophantineConsistency/AdaptiveGap85InverseOneStepChecks.lean').write_text('import DiophantineConsistency.AdaptiveGap85InverseOneStep\n#print axioms DiophantineConsistency.AdaptiveGap85InverseOneStep.one_step_gap_iff_candidate\n#print axioms DiophantineConsistency.AdaptiveGap85InverseOneStep.one_step_gap_zero_to_86\n#check DiophantineConsistency.AdaptiveGap85InverseOneStep.one_step_gap_iff_candidate\n#check DiophantineConsistency.AdaptiveGap85InverseOneStep.one_step_gap_zero_to_86\n')
env=dict(os.environ,LEAN_PATH=':'.join(map(str,[lib,*boundary])),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
s={'status':'RUNNING','root':str(w),'provider':str(provider),'parent_project_object_count':len(objects),'anchors':anchors,'boundary':list(map(str,boundary)),'records':[],'scope':'In every IΣ₁ model, for a positive tuple outside the gap with J*beta≥2, a positive one-step gap endpoint among the three shifts or their inverses exists iff the explicit inverse-old candidate is positive and in the gap. For a full 85-zero this condition yields a shifted natural 86-zero. Existence of such a step remains unproved. Three orbit modules are rebuilt from source on the selected inverse-old parent; other project/package transitive source ancestry is historical.'}
def save():(w/'state.json').write_text(json.dumps(s,indent=2)+'\n')
def audit():
 for p,h in anchors.items():
  if not Path(p).is_file() or sha(p)!=h:raise RuntimeError('guard changed: '+p)
 for name,f in zip(names,sources):
  if sha(src/'DiophantineConsistency'/(name+'.lean'))!=anchors[str(f)]:raise RuntimeError('source snapshot changed '+name)
save();print('ROOT',w,'PARENT_OBJECTS',len(objects),flush=True)
try:
 audit()
 for name in [*names,'AdaptiveGap85InverseOneStepChecks']:
  f=src/'DiophantineConsistency'/(name+'.lean');o=lib/'DiophantineConsistency'/(name+'.olean');l=logs/(name+'.log')
  with l.open('w') as out:r=subprocess.run([str(LEAN),'-M6000','-j1','-DElab.async=false','--root='+str(src),str(f),'-o',str(o)],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
  content=l.read_text();s['records'].append({'module':name,'exit':r.returncode,'source_sha256':sha(f),'object_sha256':sha(o) if o.exists() else None,'log_sha256':sha(l),'warnings':content.count('warning:')});save()
  if r.returncode or 'sorryAx' in content or 'error:' in content or 'warning:' in content:raise RuntimeError('compile failed '+name+': '+content)
  if name.endswith('Checks'):
   axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',content,re.S)
   if len(axioms)!=2 or any({a.strip() for a in x.split(',') if a.strip()}-{'propext','Classical.choice','Quot.sound'} for x in axioms):raise RuntimeError('unexpected axiom report')
 audit()
 for row in s['records']:
  if sha(lib/'DiophantineConsistency'/(row['module']+'.olean'))!=row['object_sha256'] or sha(logs/(row['module']+'.log'))!=row['log_sha256']:raise RuntimeError('output changed')
 s['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:
 s.update(status='FAILED',failure=str(e));save();print('FAILED',str(e),flush=True);raise
