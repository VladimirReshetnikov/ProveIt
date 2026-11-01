#!/usr/bin/env python3
"""Independent post-run audit of first-score provider union and replay rows."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

D = Path(__file__).resolve().parent
V = D.parent
I = V/'adaptive-gap85-first-score-input'
C = V/'adaptive-gap85-score-cantor-repair'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
m = json.loads((I/'manifest.json').read_text())
c = json.loads((D/'comparison.json').read_text())
t = json.loads((D/'terminal.json').read_text())
cm = json.loads((C/'manifest.json').read_text())
assert c['status']=='MATCHED_PASS' and t['status']=='PASS_EXIT_0_OBSERVED'
assert c['manifest_sha256']==sha(I/'manifest.json')==t['manifest_sha256']
assert t['comparison_sha256']==sha(D/'comparison.json')
assert all(t[k]['exit_code']==0 for k in ('author','peer','comparator'))
assert sha(I/'replay.py')==m['driver_sha256'] and sha(I/'prepare.py')==m['preparer_sha256']
assert sha(C/'manifest.json')==m['cantor_manifest_sha256']
assert sha(C/'comparison.json')==m['cantor_comparison_sha256']
for name,digest in m['guard'].items():
    assert Path(name).is_file() and sha(name)==digest, name
def audit_candidates(entries):
    for name,expected in entries.items():
        p=Path(name)
        if expected is None:
            assert not os.path.lexists(p),name
        else:
            assert p.is_file() and str(p.resolve())==expected['resolved'] and sha(p)==expected['sha256'],name
audit_candidates(m['candidates'])
for entries in cm['candidates'].values():audit_candidates(entries)
parents=[Path(m['score_parent']),Path(m['third_parent'])]
for root,digest,entries in zip(parents,m['parent_states'],m['parent_entries']):
    assert sha(root/'state.json')==digest
    assert {p.name:str(p.resolve()) for p in (root/'lib').iterdir()
            if p.name!='DiophantineConsistency'}==m['namespace']
    actual={p.name:{'resolved':str(p.resolve()),'sha256':sha(p)}
            for p in (root/'lib/DiophantineConsistency').iterdir() if p.is_file()}
    assert actual==entries
shared=set(m['parent_entries'][0])&set(m['parent_entries'][1])
assert len(shared)==m['shared_entries']==392
assert all(m['parent_entries'][0][n]['sha256']==m['parent_entries'][1][n]['sha256'] for n in shared)
for side in ('author','peer'):
    root=Path(c[side]); state=json.loads((root/'state.json').read_text())
    assert state['status']=='PASS' and state['records']==c['records']
    assert sha(root/'state.json')==c[side+'_state_sha256']
    expected={name:v['resolved'] for name,v in m['selected'].items()}
    for row in c['records']:
        n=row['module']; src=root/'src/DiophantineConsistency'/(n+'.lean')
        obj=root/'lib/DiophantineConsistency'/(n+'.olean'); log=root/'logs'/(n+'.log')
        assert sha(src)==row['source_sha256'] and sha(obj)==row['object_sha256'] and sha(log)==row['log_sha256']
        assert sha(D/side/'src'/(n+'.lean'))==row['source_sha256']
        assert sha(D/side/'logs'/(n+'.log'))==row['log_sha256']
        expected[n+'.olean']=str(obj.resolve())
    actual={p.name:str(p.resolve()) for p in (root/'lib/DiophantineConsistency').iterdir()}
    assert actual==expected
    assert {p.name:str(p.resolve()) for p in (root/'lib').iterdir() if p.name!='DiophantineConsistency'}==m['namespace']
    env=dict(os.environ,LEAN_PATH=':'.join([str(root/'lib'),*m['boundary']]))
    env.pop('LEAN_SRC_PATH',None)
    for name in ('AdaptiveGap85FirstScore','AdaptiveGap85FirstScoreChecks'):
        src=root/'src/DiophantineConsistency'/(name+'.lean')
        out=subprocess.run(['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean',
                            '--root='+str(root/'src'),'--deps',str(src)],env=env,
                           capture_output=True,text=True,check=True).stdout
        actual={str(Path(line).resolve()) for line in out.splitlines()}
        init='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean/Init.olean'
        expected_deps=({init,m['selected']['AdaptiveGap85ScoreCoding.olean']['resolved'],
                        m['selected']['AdaptiveGap85ThirdMinimal.olean']['resolved']}
                       if name=='AdaptiveGap85FirstScore' else
                       {init,str((root/'lib/DiophantineConsistency/AdaptiveGap85FirstScore.olean').resolve())})
        assert actual==expected_deps,(side,name,actual,expected_deps)
report={'status':'PASS','shared_entries':len(shared),'parent_candidates':len(m['candidates']),
        'cantor_candidates':sum(map(len,cm['candidates'].values())),
        'manifest_sha256':sha(I/'manifest.json'),'comparison_sha256':sha(D/'comparison.json'),
        'auditor_sha256':sha(__file__),
        'scope':'Post-run source, direct-resolution, overlay and guarded-provider checks; transitive and dynamic ancestry inherited.'}
(D/'independent-audit.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print('PASS independent first-score audit:',len(shared),'shared entries,',len(m['candidates']),'parent candidates')
