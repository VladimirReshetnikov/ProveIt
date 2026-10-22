"""Bind accepted raw sources to the adopted checkout without rerunning Lean."""
from pathlib import Path
import hashlib, json
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
P=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase14'
S=Path('/tmp/k215-phase14-check')
read=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
adoption=read(P/'integration/adoption.json')
baseline=read('/tmp/k215-phase13-root/current-review.json')['sources']
actual=read('/tmp/k215-phase14-root/root-actual-review.json')
sources={}
for m,row in actual['sources'].items():
    current=Path(baseline[m]['current'])
    assert sha(current)==row['sha256'],m
    sources[m]={'current':str(current),'sha256':row['sha256']}
assert len(sources)==198 and 'BusyBeaver.ZFC.KProfileTC' not in sources
retired={str(R/r['path']):r for r in adoption['files'] if r['action']=='retire'}
assert len(retired)==2
for p,row in retired.items():
    assert not Path(p).exists() and not Path(p).is_symlink()
    assert sha(R/row['before_snapshot'])==row['before_sha256']
for row in adoption['files']:
    if row['action']=='replace':assert sha(R/row['path'])==row['after_sha256']
prior=read(S/'producer-boundary.json')
for p,h in prior['accepted_five_files'].items():assert sha(p)==h
for row in prior['files']:
    if row['current_state']=='absent':
        assert not Path(row['canonical']).exists() and not Path(row['canonical']).is_symlink()
runs=[]
warnings=[]
old=read('/tmp/k215-phase13-upstream-check/primary-run1/completed.json')|read('/tmp/k215-phase13-upstream-check/compatibility-run1/completed.json')
for name in ['primary-run2','compatibility-run1']:
    historical=[]
    for p,h in read(S/name/'before.json')['inputs'].items():
        if p in retired:
            row=retired[p];assert h==row['before_sha256'];historical.append({'canonical':p,'before_sha256':h,'archived_before':row['before_snapshot']})
        else:assert sha(p)==h,p
    assert len(historical)==2
    runs.append({'run':name,'intentionally_historical_retired_inputs':historical,'all_other_before_inputs_current_exact':True})
    for m,rec in read(S/name/'completed.json').items():
        n=Path(rec['log']).read_text().count('warning:')
        if n:
            assert rec['source_sha256']==old[m]['source_sha256'],m
            assert n==Path(old[m]['log']).read_text().count('warning:'),m
            warnings.append({'run':name,'module':m,'warnings':n,'source_unchanged_from_phase13':True,'origin':rec['origin']})
result={'status':'PASS_CURRENT_PHASE14_ADOPTION','adoption_sha256':sha(P/'integration/adoption.json'),'project_sources':198,'canonical_writes':7,'retirements':2,'prior_five_adoptions_unchanged':True,'runs':runs,'sources':sources}
(P/'integration/current-review.json').write_text(json.dumps(result,indent=2)+'\n')
Path('/tmp/k215-phase14-root/current-review.json').write_text(json.dumps(result,indent=2)+'\n')
(P/'integration/warning-comparison.json').write_text(json.dumps({'status':'PASS_ALL_SELECTED_WARNINGS_PREEXIST_IN_IDENTICAL_PHASE13_SOURCES','records':warnings},indent=2)+'\n')
for name in ['review_actual.py','root-actual-review.json','adopt.py','review_current.py']:
    (P/'integration'/name).write_bytes((Path('/tmp/k215-phase14-root')/name).read_bytes())
print('PASS current:198 sources;7 writes;2 retirements;prior5 unchanged')
