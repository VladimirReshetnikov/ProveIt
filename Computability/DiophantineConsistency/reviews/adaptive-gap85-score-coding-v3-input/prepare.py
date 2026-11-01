#!/usr/bin/env python3
"""Freeze inputs for score-coding v3; this does not run Lean proof checks."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
from common import CHECKS, SUFFIXES, companion_candidates, describe, direct_entries, sha, verify_candidates

D=Path(__file__).resolve().parent;R=D.parents[3]
SRC=R/'Computability/DiophantineConsistency/research/adaptive-gap85-normalization/AdaptiveGap85ScoreCoding.lean'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
P=Path('/tmp/gap85-balance-least-replay-75g18vpi')
BS=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl/state.json')
REPAIR=R/'Computability/DiophantineConsistency/reviews/adaptive-gap85-score-cantor-repair'
RM=REPAIR/'manifest.json';RR=REPAIR/'comparison.json';RT=REPAIR/'terminal.json'
read=lambda p:json.loads(Path(p).read_text())
rm,rr,rt,parent=map(read,(RM,RR,RT,P/'state.json'))
assert parent['status']=='PASS' and len(parent['records'])==2
assert rr['status']=='MATCHED_PASS' and rr['manifest_sha256']==sha(RM)
assert rt['status']=='PASS_EXIT_0_OBSERVED' and rt['manifest_sha256']==sha(RM) and rt['comparison_sha256']==sha(RR)
assert all(rt[x]['exit_code']==0 for x in ('author','peer','comparator','independent_packet_audit'))
assert rr['object_sha256']==rm['expected_olean_sha256'] and rr['original_provider_status']=='FAILED'
assert rm['score_parent']==str(P) and rm['selected']['BusyBeaver.ZFC.ArithmeticCantor']['logical']==str(P/'lib/BusyBeaver/ZFC/ArithmeticCantor.olean')
assert sha(REPAIR/'compare.py')==rr['compare_sha256']
for side in ('author','peer'):
    assert sha(REPAIR/side/'state.json')==rr[side+'_state_sha256']
    assert sha(REPAIR/side/'ArithmeticCantor.olean')==rr['object_sha256']
    assert sha(REPAIR/side/'ArithmeticCantor.lean')==rr['source_sha256']
    assert sha(REPAIR/side/'lean.log')==rr['full_log_sha256']
for path,digest in rm['guard'].items():assert Path(path).is_file() and sha(path)==digest,path
for candidates in rm['candidates'].values():
    for path,info in candidates.items():
        p=Path(path)
        if info is None:assert not os.path.lexists(p),path
        else:assert p.is_file() and str(p.resolve())==info['resolved'] and sha(p)==info['sha256'],path
roots=[str(P/'lib'),*read(BS)['boundary']]
assert roots==rm['roots'] and len(roots)==len(set(roots))
provider_root=direct_entries(P/'lib'); provider_project=direct_entries(P/'lib/DiophantineConsistency')
assert all(v['kind'] in ('file','symlink') and 'sha256' in v for v in provider_project.values())
row=next(x for x in parent['records'] if x['module']=='AdaptiveGap85BalanceLeast')
assert row['exit']==0 and sha(P/'lib/DiophantineConsistency/AdaptiveGap85BalanceLeast.olean')==row['object_sha256']
scoremods=('DiophantineConsistency.AdaptiveGap85BalanceLeast',
           'DiophantineConsistency.AdaptiveGap85ScoreCoding',
           'DiophantineConsistency.AdaptiveGap85ScoreCodingChecks')
score_candidates=companion_candidates(roots,scoremods)
for mod in scoremods[1:]:
    for root in roots:
        assert score_candidates[str(Path(root)/(mod.replace('.','/')+'.olean'))] is None,('output shadow',root,mod)
modules=sorted({name[:-len('.olean')] for name in provider_project if name.endswith('.olean')})
companion={str(P/'lib/DiophantineConsistency'/(module+s)):describe(P/'lib/DiophantineConsistency'/(module+s))
           for module in modules for s in SUFFIXES}
source=SRC.read_bytes();source_sha=hashlib.sha256(source).hexdigest()
guardpaths=[D/'prepare.py',D/'replay.py',D/'common.py',SRC,LEAN,BS,P/'state.json',RM,RR,RT,
            REPAIR/'prepare.py',REPAIR/'replay.py',REPAIR/'compare.py']
for side in ('author','peer'):
    guardpaths += [REPAIR/side/'state.json',REPAIR/side/'ArithmeticCantor.lean',
                   REPAIR/side/'ArithmeticCantor.olean',REPAIR/side/'lean.log']
guard={str(p):describe(p) for p in guardpaths}
assert all(v is not None and 'sha256' in v for v in guard.values())
assert describe(SRC)['kind']=='file' and SRC.resolve()==SRC
env=dict(os.environ,LEAN_PATH=':'.join(roots),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
deps=subprocess.run([str(LEAN),'--deps',str(SRC)],cwd=R,env=env,capture_output=True,text=True,check=True)
expected=[rm['selected']['Init']['logical'],rm['selected']['Init']['logical'],
          str(P/'lib/DiophantineConsistency/AdaptiveGap85BalanceLeast.olean'),
          rm['selected']['BusyBeaver.ZFC.ArithmeticCantor']['logical']]
assert deps.stdout.splitlines()==expected and not deps.stderr,(deps.stdout,deps.stderr)
for path,expected in guard.items():assert describe(path)==expected,path
verify_candidates(score_candidates);verify_candidates(companion)
assert direct_entries(P/'lib')==provider_root and direct_entries(P/'lib/DiophantineConsistency')==provider_project
for path,digest in rm['guard'].items():assert sha(path)==digest,path
for candidates in rm['candidates'].values():
    for path,info in candidates.items():
        p=Path(path)
        if info is None:assert not os.path.lexists(p),path
        else:assert p.is_file() and str(p.resolve())==info['resolved'] and sha(p)==info['sha256'],path
snapshot=D/'sources/DiophantineConsistency';assert not snapshot.exists();snapshot.mkdir(parents=True)
(snapshot/'AdaptiveGap85ScoreCoding.lean').write_bytes(source)
(snapshot/'AdaptiveGap85ScoreCodingChecks.lean').write_bytes(CHECKS)
manifest={'schema':'score-coding-guarded-v3','root':str(R),'provider':str(P),'lean':str(LEAN),
          'roots':roots,'guard':guard,'repair_manifest':str(RM),'repair_receipt':str(RR),'repair_terminal':str(RT),
          'provider_root':provider_root,'provider_project':provider_project,'provider_companions':companion,
          'score_candidates':score_candidates,'score_source_sha256':source_sha,
          'checks_source_sha256':hashlib.sha256(CHECKS).hexdigest(),
          'preparer_sha256':sha(D/'prepare.py'),'driver_sha256':sha(D/'replay.py'),'common_sha256':sha(D/'common.py'),
          'deps_provider_stdout':deps.stdout,
          'scope':'Exact source and private-overlay direct resolution guarded; Cantor direct-input reproduction gated. '
                  'Historical transitive project/package source-to-object and dynamic ancestry remains inherited.'}
out=D/'manifest.json';assert not out.exists();out.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print('PREPARED',sha(out),'provider_entries',len(provider_project),'provider_companions',len(companion),
      'score_candidates',len(score_candidates),'cantor_candidates',sum(map(len,rm['candidates'].values())))
