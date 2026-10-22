"""Bind actual checked sources and historical before-inputs to exact adoption."""
from pathlib import Path
import argparse,hashlib,json
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');O=Path('/tmp/k215-phase15-root')
P=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase15'
S=Path('/tmp/k215-phase15-check')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
ap=argparse.ArgumentParser();ap.add_argument('--primary',required=True);a=ap.parse_args()
adoption=read(P/'integration/adoption.json');actual=read(O/'root-actual-review.json')
baseline=read('/tmp/k215-phase14-root/current-review.json')['sources']
rows={r['path']:r for r in adoption['files']}
new=next(r for r in adoption['files'] if r['action']=='create')
assert len(rows)==10 and Path(new['path']).name=='PowerSets.lean'
sources={}
for m,r in actual['sources'].items():
    current=Path(baseline[m]['current']) if m in baseline else R/new['path']
    assert sha(current)==r['sha256']
    sources[m]={'current':str(current),'sha256':r['sha256']}
assert len(sources)==199 and 'BusyBeaver.ZFC.KProfileTC' not in sources
for r in adoption['files']:
    assert sha(R/r['path'])==r['after_sha256']
    if r['before_snapshot']:assert sha(R/r['before_snapshot'])==r['before_sha256']
prior=read(S/'producer-boundary.json')
for p,h in prior['accepted_five_files'].items():assert sha(p)==h
absent=[]
for p in prior['absent_inputs']:
    if p==str(R/new['path']):assert sha(p)==new['after_sha256']
    else:assert not Path(p).exists() and not Path(p).is_symlink();absent.append(p)
assert len(absent)==4
runs=[];warnings=[]
old=read('/tmp/k215-phase14-check/primary-run2/completed.json')|read('/tmp/k215-phase14-check/compatibility-run1/completed.json')
warning_messages=lambda p:[l.split(': warning:',1)[1] for l in Path(p).read_text().splitlines() if ': warning:' in l]
for name in ['primary-run1','primary-run2',a.primary,'compatibility-run1']:
    historical=[];before=read(S/name/'before.json')
    for p,h in before['inputs'].items():
        rel=str(Path(p).relative_to(R)) if Path(p).is_relative_to(R) else None
        if rel in rows:
            r=rows[rel];assert r['before_sha256']==h and sha(R/r['before_snapshot'])==h
            historical.append({'canonical':p,'before_sha256':h,'archived_before':r['before_snapshot']})
        else:assert sha(p)==h,p
    assert len(historical)==9
    for p in before['absent_inputs']:
        if p==str(R/new['path']):assert sha(p)==new['after_sha256']
        else:assert not Path(p).exists() and not Path(p).is_symlink()
    runs.append({'run':name,'intentionally_historical_before_inputs':historical,'new_PowerSets_absence_is_historical':True,'all_other_before_inputs_current_exact':True})
    if name not in [a.primary,'compatibility-run1']:continue
    for m,rec in read(S/name/'completed.json').items():
        messages=warning_messages(rec['log'])
        if messages:
            assert m in old and messages==warning_messages(old[m]['log']),m
            warnings.append({'run':name,'module':m,'warnings':len(messages),'messages':messages,
                             'source_unchanged':rec['source_sha256']==old[m]['source_sha256'],'origin':rec['origin']})
record={'status':'PASS_CURRENT_PHASE15_ADOPTION','adoption_sha256':sha(P/'integration/adoption.json'),
    'project_sources':199,'canonical_writes':10,'retirements':0,'prior_five_adoptions_unchanged':True,
    'prior_four_absences_retained':absent,'runs':runs,'sources':sources}
(P/'integration/current-review.json').write_text(json.dumps(record,indent=2)+'\n')
(O/'current-review.json').write_text(json.dumps(record,indent=2)+'\n')
(P/'integration/warning-comparison.json').write_text(json.dumps({'status':'PASS_ALL_SELECTED_WARNING_MESSAGES_PREEXIST_IN_PHASE14','records':warnings},indent=2)+'\n')
for name in ['review_actual.py','root-actual-review.json','adopt.py','review_current.py']:
    (P/'integration'/name).write_bytes((O/name).read_bytes())
print('PASS current:199sources,10writes,4priorabsences,allwarningmessagespreexisting')
