#!/usr/bin/env python3
"""Guarded focused replay; inherited project and package ancestry is not authenticated."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
S=R/'Computability/DiophantineConsistency/research/adaptive-gap85-normalization/AdaptiveGap85PositiveModular.lean'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
provider=Path('/tmp/adaptive-gap85-machine-m09n4q_7/lib')
boundary=[Path(p) for p in json.load(open('/tmp/adaptive13-assembly-recomposed-q9s50zdl/state.json'))['boundary']]
direct=provider/'DiophantineConsistency/ArithmeticPellResidueClasses.olean'
assert direct.is_file()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
files=[S,LEAN,*sorted(p for p in direct.parent.glob(direct.name+'*') if p.is_file())]
anchors={str(p):sha(p) for p in files}
w=Path(tempfile.mkdtemp(prefix='gap85-positive-modular-replay-'));src=w/'src';lib=w/'lib';logs=w/'logs'
for p in [src/'DiophantineConsistency',lib/'DiophantineConsistency',logs]:p.mkdir(parents=True,exist_ok=True)
for p in provider.iterdir():
 if p.name!='DiophantineConsistency': (lib/p.name).symlink_to(p, target_is_directory=p.is_dir())
for p in (provider/'DiophantineConsistency').iterdir():
 (lib/'DiophantineConsistency'/p.name).symlink_to(p, target_is_directory=p.is_dir())
shutil.copyfile(S,src/'DiophantineConsistency/AdaptiveGap85PositiveModular.lean')
(src/'DiophantineConsistency/AdaptiveGap85PositiveModularChecks.lean').write_text('import DiophantineConsistency.AdaptiveGap85PositiveModular\n#print axioms DiophantineConsistency.AdaptiveGap85PositiveModular.positive_root_cubic_congruence\n#check DiophantineConsistency.AdaptiveGap85PositiveModular.positive_root_cubic_congruence\n')
env=dict(os.environ,LEAN_PATH=':'.join(map(str,[lib,provider,*boundary])),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
s={'status':'RUNNING','root':str(w),'anchors':anchors,'provider':str(provider),'boundary':list(map(str,boundary)),'records':[],'scope':'Subtraction-free positive-template cubic congruence in IΣ₁ models under the explicit root and divisibility assumptions. Exact direct project object guarded; its transitive project ancestry and external package ancestry inherited. Does not prove special-template existence or full 85 equivalence.'}
def save():(w/'state.json').write_text(json.dumps(s,indent=2)+'\n')
def audit():
 for p,h in anchors.items():
  if not Path(p).is_file() or sha(p)!=h:raise RuntimeError('guard changed: '+p)
 if sha(src/'DiophantineConsistency/AdaptiveGap85PositiveModular.lean')!=anchors[str(S)]:raise RuntimeError('source snapshot changed')
save();print('ROOT',w,flush=True)
try:
 audit()
 for name in ['AdaptiveGap85PositiveModular','AdaptiveGap85PositiveModularChecks']:
  f=src/'DiophantineConsistency'/(name+'.lean');o=lib/'DiophantineConsistency'/(name+'.olean');l=logs/(name+'.log')
  with l.open('w') as out:r=subprocess.run([str(LEAN),'-M6000','-j1','-DElab.async=false','--root='+str(src),str(f),'-o',str(o)],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
  content=l.read_text();s['records'].append({'module':name,'exit':r.returncode,'source_sha256':sha(f),'object_sha256':sha(o) if o.exists() else None,'log_sha256':sha(l)});save()
  if r.returncode or 'sorryAx' in content or 'error:' in content:raise RuntimeError('compile failed '+name+': '+content)
  if name.endswith('Checks'):
   axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',content,re.S)
   if len(axioms)!=1 or any({a.strip() for a in x.split(',') if a.strip()}-{'propext','Classical.choice','Quot.sound'} for x in axioms):raise RuntimeError('unexpected axiom report')
 audit()
 for row in s['records']:
  if sha(lib/'DiophantineConsistency'/(row['module']+'.olean'))!=row['object_sha256'] or sha(logs/(row['module']+'.log'))!=row['log_sha256']:raise RuntimeError('output changed')
 s['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:
 s.update(status='FAILED',failure=str(e));save();print('FAILED',str(e),flush=True);raise
