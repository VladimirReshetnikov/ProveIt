#!/usr/bin/env python3
"""Two-module exploratory replay; direct Mathlib objects are pinned, transitive package ancestry inherited."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
S=R/'Computability/DiophantineConsistency/research/adaptive-gap85-normalization/AdaptiveGap85LargeYPowNormExample.lean'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
BASE=Path('/home/codex/src/Proofs/.lake/packages');names=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']
packages=[BASE/n/'.lake/build/lib/lean' for n in names]+[LEAN.parent.parent/'lib/lean']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
math=packages[-2];direct=[]
for stem in ['Mathlib/Tactic/NormNum','Mathlib/Tactic/IntervalCases']:
 f=math/(stem+'.olean');assert f.is_file(),f
 direct.extend(x for x in f.parent.glob(f.name+'*') if x.is_file())
anchors={str(p):sha(p) for p in [S,LEAN,*sorted(set(direct))]}
w=Path(tempfile.mkdtemp(prefix='gap85-large-Y-power-example-replay-'));src=w/'src';lib=w/'lib';logs=w/'logs'
for p in [src,lib,logs]:p.mkdir()
shutil.copyfile(S,src/'AdaptiveGap85LargeYPowNormExample.lean')
(src/'AdaptiveGap85LargeYPowNormExampleChecks.lean').write_text('import AdaptiveGap85LargeYPowNormExample\n#print axioms AdaptiveGap85LargeYPowNormExample.parameters\n#print axioms AdaptiveGap85LargeYPowNormExample.two_norms\n#print axioms AdaptiveGap85LargeYPowNormExample.index_polynomials\n#print axioms AdaptiveGap85LargeYPowNormExample.no_nontrivial_cube\n')
env=dict(os.environ,LEAN_PATH=':'.join(map(str,[lib,*packages])),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
s={'status':'RUNNING','root':str(w),'anchors':anchors,'package_paths':[str(p) for p in packages],'records':[],'scope':'Concrete X=2^m large-Y partial Pell configuration, explicitly failing nontrivial cubic divisibility; not a full 85 zero or current-port result. Direct Mathlib objects and companions guarded; package-transitive ancestry inherited.'}
def save():(w/'state.json').write_text(json.dumps(s,indent=2)+'\n')
def audit():
 for p,h in anchors.items():
  if not Path(p).is_file() or sha(p)!=h:raise RuntimeError('guard changed: '+p)
 if sha(src/'AdaptiveGap85LargeYPowNormExample.lean')!=anchors[str(S)]:raise RuntimeError('source snapshot changed')
save();print('ROOT',w,flush=True)
try:
 audit()
 for name in ['AdaptiveGap85LargeYPowNormExample','AdaptiveGap85LargeYPowNormExampleChecks']:
  f=src/(name+'.lean');o=lib/(name+'.olean');l=logs/(name+'.log')
  with l.open('w') as out:r=subprocess.run([str(LEAN),'-M4000','-j1','-DElab.async=false','--root='+str(src),str(f),'-o',str(o)],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
  content=l.read_text();s['records'].append({'module':name,'exit':r.returncode,'source_sha256':sha(f),'object_sha256':sha(o) if o.exists() else None,'log_sha256':sha(l)});save()
  if r.returncode or 'sorryAx' in content or 'error:' in content:raise RuntimeError('compile failed '+name+': '+content)
  if name.endswith('Checks'):
   import re
   axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',content,re.S)
   if len(axioms)!=4 or any({a.strip() for a in x.split(',') if a.strip()}-{'propext','Classical.choice','Quot.sound'} for x in axioms):raise RuntimeError('unexpected axiom report')
 audit()
 for row in s['records']:
  if sha(lib/(row['module']+'.olean'))!=row['object_sha256'] or sha(logs/(row['module']+'.log'))!=row['log_sha256']:raise RuntimeError('output changed')
 s['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:
 s.update(status='FAILED',failure=str(e));save();print('FAILED',str(e),flush=True);raise
