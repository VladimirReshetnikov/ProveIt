#!/usr/bin/env python3
"""Source-directed 85 zero-score coding replay on a matched historical provider."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
SRC=R/'Computability/DiophantineConsistency/research/adaptive-gap85-normalization'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
provider=Path('/tmp/gap85-balance-least-replay-75g18vpi')
boundary=[Path(p) for p in json.load(open('/tmp/adaptive13-assembly-recomposed-q9s50zdl/state.json'))['boundary']]
names=['AdaptiveGap85ScoreCoding']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
objects=sorted(p for p in (provider/'lib/DiophantineConsistency').glob('*.olean*') if p.is_file())
assert json.load(open(provider/'state.json'))['status']=='PASS'
assert len(json.load(open(provider/'state.json'))['records'])==2
external=provider/'lib/Foundation/FirstOrder/Arithmetic/HFS/PRF.olean'
assert external.is_file()
files=[Path(__file__).resolve(),LEAN,provider/'state.json',external,*[SRC/(n+'.lean') for n in names],*objects]
repair=R/'Computability/DiophantineConsistency/reviews/adaptive-gap85-score-cantor-repair'
repair_manifest=repair/'manifest.json';repair_receipt=repair/'comparison.json'
rm=json.loads(repair_manifest.read_text());rr=json.loads(repair_receipt.read_text())
terminal=repair/'terminal.json';tr=json.loads(terminal.read_text())
assert rr['status']=='MATCHED_PASS' and rr['manifest_sha256']==sha(repair_manifest)
assert tr['status']=='PASS_EXIT_0_OBSERVED' and tr['manifest_sha256']==sha(repair_manifest) and tr['comparison_sha256']==sha(repair_receipt)
assert all(tr[key]['exit_code']==0 for key in ('author','peer','comparator','independent_packet_audit'))
assert rr['object_sha256']==rm['expected_olean_sha256'] and rm['score_parent']==str(provider)
assert rr['original_provider_status']=='FAILED'
assert rm['selected']['BusyBeaver.ZFC.ArithmeticCantor']['logical']==str(provider/'lib/BusyBeaver/ZFC/ArithmeticCantor.olean')
files += [repair_manifest,repair_receipt,terminal,repair/'compare.py',repair/'replay.py',repair/'prepare.py',
          repair/'author/state.json',repair/'peer/state.json',repair/'author/ArithmeticCantor.olean',
          repair/'peer/ArithmeticCantor.olean',repair/'author/lean.log',repair/'peer/lean.log']
assert sha(repair/'compare.py')==rr['compare_sha256']
assert sha(repair/'author/state.json')==rr['author_state_sha256'] and sha(repair/'peer/state.json')==rr['peer_state_sha256']
assert sha(repair/'author/lean.log')==sha(repair/'peer/lean.log')==rr['full_log_sha256']
assert sha(repair/'author/ArithmeticCantor.olean')==sha(repair/'peer/ArithmeticCantor.olean')==rr['object_sha256']
anchors={str(p):sha(p) for p in files}
w=Path(tempfile.mkdtemp(prefix='gap85-score-coding-guarded-replay-'));src=w/'src';lib=w/'lib';logs=w/'logs'
for p in [src/'DiophantineConsistency',lib/'DiophantineConsistency',logs]:p.mkdir(parents=True,exist_ok=True)
for p in (provider/'lib').iterdir():
 if p.name!='DiophantineConsistency': (lib/p.name).symlink_to(p, target_is_directory=p.is_dir())
for p in (provider/'lib/DiophantineConsistency').iterdir():
 if not any(p.name.startswith(n+'.') for n in names): (lib/'DiophantineConsistency'/p.name).symlink_to(p, target_is_directory=p.is_dir())
for n in names:shutil.copyfile(SRC/(n+'.lean'),src/'DiophantineConsistency'/(n+'.lean'))
(src/'DiophantineConsistency/AdaptiveGap85ScoreCodingChecks.lean').write_text('import DiophantineConsistency.AdaptiveGap85ScoreCoding\n#print axioms DiophantineConsistency.AdaptiveGap85ScoreCoding.zeroScore_definable\n#print axioms DiophantineConsistency.AdaptiveGap85ScoreCoding.exists_minimizing_zero\n#print axioms DiophantineConsistency.AdaptiveGap85ScoreCoding.exists_minimal_blocked_unconditional\n#check DiophantineConsistency.AdaptiveGap85ScoreCoding.exists_minimal_blocked_unconditional\n')
env=dict(os.environ,LEAN_PATH=':'.join(map(str,[lib,*boundary])),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
s={'status':'RUNNING','root':str(w),'provider':str(provider),'parent_project_object_count':len(objects),'anchors':anchors,'boundary':list(map(str,boundary)),'records':[],'cantor_repair_manifest_sha256':sha(repair_manifest),'cantor_repair_receipt_sha256':sha(repair_receipt),'scope':'For the actual 85 literal, zero scores are Sigma-one definable and any nonempty score set has a minimum with an explicit balance blocker; zero existence, normalization and the 85 equivalence remain open. The directly imported Cantor object is guarded and byte-identically rebuilt in two checked direct-input replays; the original provider failed later. Selected inherited project objects pinned; original transitive project/package source ancestry historical.'}
def save():(w/'state.json').write_text(json.dumps(s,indent=2)+'\n')
def audit():
 for path, expected in rm['guard'].items():
  if not Path(path).is_file() or sha(path)!=expected:raise RuntimeError('Cantor repair guard changed: '+path)
 for module, candidates in rm['candidates'].items():
  for path, expected in candidates.items():
   if expected is None:
    if os.path.lexists(path):raise RuntimeError('new Cantor candidate appeared: '+path)
   elif not Path(path).is_file() or str(Path(path).resolve())!=expected['resolved'] or sha(path)!=expected['sha256']:
    raise RuntimeError('Cantor candidate changed: '+path)
 for p,h in anchors.items():
  if not Path(p).is_file() or sha(p)!=h:raise RuntimeError('guard changed: '+p)
 for n in names:
  if sha(src/'DiophantineConsistency'/(n+'.lean'))!=anchors[str(SRC/(n+'.lean'))]:raise RuntimeError('source snapshot changed '+n)
save();print('ROOT',w,'PARENT_OBJECTS',len(objects),flush=True)
try:
 audit()
 for name in [*names,'AdaptiveGap85ScoreCodingChecks']:
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
