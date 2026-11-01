#!/usr/bin/env python3
"""Source-directed third-model replay on a matched historical provider."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
SRC=R/'Computability/DiophantineConsistency/research/adaptive-gap85-normalization'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
provider=Path('/tmp/gap85-third-model-replay-1e2nemk4')
boundary=[Path(p) for p in json.load(open('/tmp/adaptive13-assembly-recomposed-q9s50zdl/state.json'))['boundary']]
names=['AdaptiveGap85JointResidue']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
objects=sorted(p for p in (provider/'lib/DiophantineConsistency').glob('*.olean*') if p.is_file())
assert json.load(open(provider/'state.json'))['status']=='PASS'
assert len(json.load(open(provider/'state.json'))['records'])==2
external=provider/'lib/Foundation/FirstOrder/Arithmetic/HFS/PRF.olean'
assert external.is_file()
files=[Path(__file__).resolve(),LEAN,provider/'state.json',external,*[SRC/(n+'.lean') for n in names],*objects]
anchors={str(p):sha(p) for p in files}
w=Path(tempfile.mkdtemp(prefix='gap85-joint-residue-replay-'));src=w/'src';lib=w/'lib';logs=w/'logs'
for p in [src/'DiophantineConsistency',lib/'DiophantineConsistency',logs]:p.mkdir(parents=True,exist_ok=True)
for p in (provider/'lib').iterdir():
 if p.name!='DiophantineConsistency': (lib/p.name).symlink_to(p, target_is_directory=p.is_dir())
for p in (provider/'lib/DiophantineConsistency').iterdir():
 if not any(p.name.startswith(n+'.') for n in names): (lib/'DiophantineConsistency'/p.name).symlink_to(p, target_is_directory=p.is_dir())
for n in names:shutil.copyfile(SRC/(n+'.lean'),src/'DiophantineConsistency'/(n+'.lean'))
(src/'DiophantineConsistency/AdaptiveGap85JointResidueChecks.lean').write_text('import DiophantineConsistency.AdaptiveGap85JointResidue\n#print axioms DiophantineConsistency.AdaptiveGap85JointResidue.old_joint\n#print axioms DiophantineConsistency.AdaptiveGap85JointResidue.balance_joint\n#print axioms DiophantineConsistency.AdaptiveGap85JointResidue.third_joint\n#print axioms DiophantineConsistency.AdaptiveGap85JointResidue.literal_orbit_joint\n#print axioms DiophantineConsistency.AdaptiveGap85JointResidue.literal_orbit_congruence\n')
env=dict(os.environ,LEAN_PATH=':'.join(map(str,[lib,*boundary])),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
s={'status':'RUNNING','root':str(w),'provider':str(provider),'parent_project_object_count':len(objects),'anchors':anchors,'boundary':list(map(str,boundary)),'records':[],'scope':'Joint-residue congruence for finite external coordinate-shift sequences under explicit balance-C and third-bA/F subtraction bounds; no zero-preservation, zero-existence or 85 equivalence claim. Selected inherited project objects pinned; original transitive project/package source ancestry historical.'}
def save():(w/'state.json').write_text(json.dumps(s,indent=2)+'\n')
def audit():
 for p,h in anchors.items():
  if not Path(p).is_file() or sha(p)!=h:raise RuntimeError('guard changed: '+p)
 for n in names:
  if sha(src/'DiophantineConsistency'/(n+'.lean'))!=anchors[str(SRC/(n+'.lean'))]:raise RuntimeError('source snapshot changed '+n)
save();print('ROOT',w,'PARENT_OBJECTS',len(objects),flush=True)
try:
 audit()
 for name in [*names,'AdaptiveGap85JointResidueChecks']:
  f=src/'DiophantineConsistency'/(name+'.lean');o=lib/'DiophantineConsistency'/(name+'.olean');l=logs/(name+'.log')
  with l.open('w') as out:r=subprocess.run([str(LEAN),'-M6000','-j1','-DElab.async=false','--root='+str(src),str(f),'-o',str(o)],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
  content=l.read_text();s['records'].append({'module':name,'exit':r.returncode,'source_sha256':sha(f),'object_sha256':sha(o) if o.exists() else None,'log_sha256':sha(l),'warnings':content.count('warning:')});save()
  if r.returncode or 'sorryAx' in content or 'error:' in content or 'warning:' in content:raise RuntimeError('compile failed '+name+': '+content)
  if name.endswith('Checks'):
   axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',content,re.S)
   if len(axioms)!=5 or any({a.strip() for a in x.split(',') if a.strip()}-{'propext','Classical.choice','Quot.sound'} for x in axioms):raise RuntimeError('unexpected axiom report')
 audit()
 for row in s['records']:
  if sha(lib/'DiophantineConsistency'/(row['module']+'.olean'))!=row['object_sha256'] or sha(logs/(row['module']+'.log'))!=row['log_sha256']:raise RuntimeError('output changed')
 s['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:
 s.update(status='FAILED',failure=str(e));save();print('FAILED',str(e),flush=True);raise
