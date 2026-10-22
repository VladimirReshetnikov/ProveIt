"""Adopt only the exact compiled phase15 sources and reproduced maintained producer."""
from pathlib import Path
import hashlib,json
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
S=Path('/tmp/k215-phase15-retry');O=Path('/tmp/k215-phase15-root')
P=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase15'
read=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert read(O/'root-actual-review.json')['status']=='PASS_ROOT_RAW_PHASE15_ACTUAL'
sources=read(S/'sources.json');assert len(sources)==9
baseline=read('/tmp/k215-phase14-root/current-review.json')['sources']
for row in baseline.values():assert sha(row['current'])==row['sha256']
writes=[]
for row in sources:
    current=R/row['canonical'];candidate=Path(row['source'])
    assert sha(candidate)==row['source_sha256']
    if row['before_sha256'] is None:assert not current.exists() and not current.is_symlink()
    else:assert sha(current)==row['before_sha256']==baseline[row['module']]['sha256']
    writes.append((current,candidate,row['before_sha256']))
producer=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/generate_kq1.py'
candidate=Path('/tmp/k215-phase15-quotient/candidate/Computability/BusyBeaver/Research/ZFC/k225-formal/generate_kq1.py')
assert sha(producer)=='f59ee6c64ce19cc5609cfca3cc678969450851d54d9ff0e1416fcd1e1afc8561'
assert sha(candidate)=='8837ba3cbe0a82c4f166160f58d39ef35bd9d5d50adcac5078d4cf26eaaf7e42'
assert sha('/tmp/k215-phase15-quotient/reproduction/actual.json')=='dc9ac93fa79c8e817674eceeebcf31d78c6e9a57886570a431e32b6e5155bc96'
writes.append((producer,candidate,sha(producer)))
assert len({p for p,_,_ in writes})==10 and not P.exists()
records=[];metrics={'lean':{'before_bytes':0,'after_bytes':0,'before_lines':0,'after_lines':0},
                    'producer':{'before_bytes':0,'after_bytes':0,'before_lines':0,'after_lines':0}}
for current,candidate,before_sha in writes:
    relative=current.relative_to(R);before=current.read_bytes() if before_sha else b'';after=candidate.read_bytes()
    archived=None
    if before_sha:
        path=P/'integration/before'/relative;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(before)
        archived=str(path.relative_to(R))
    kind='lean' if current.suffix=='.lean' else 'producer';m=metrics[kind]
    m['before_bytes']+=len(before);m['after_bytes']+=len(after)
    m['before_lines']+=len(before.splitlines());m['after_lines']+=len(after.splitlines())
    records.append({'path':str(relative),'before_sha256':before_sha,'after_sha256':sha(candidate),
                    'before_snapshot':archived,'candidate':str(candidate),'action':'replace' if before_sha else 'create'})
for current,candidate,_ in writes:
    current.parent.mkdir(parents=True,exist_ok=True);current.write_bytes(candidate.read_bytes())
for row in records:assert sha(R/row['path'])==row['after_sha256']
for m in metrics.values():m.update(bytes_saved=m['before_bytes']-m['after_bytes'],lines_saved=m['before_lines']-m['after_lines'])
record={'status':'ADOPTED_EXACT_CHECKED_PHASE15','files':records,'source_writes':9,'producer_writes':1,'retirements':0,
    'metrics':metrics,'scope':'Nine compiled Lean sources, including the one-line explicit import repair and exact Source193 dense bridge, plus the reproduced maintained quotient producer. Machine and external endpoint types unchanged.'}
(P/'integration/adoption.json').write_text(json.dumps(record,indent=2)+'\n')
(O/'adoption.json').write_text(json.dumps(record,indent=2)+'\n')
print('ADOPTED',json.dumps(metrics))
