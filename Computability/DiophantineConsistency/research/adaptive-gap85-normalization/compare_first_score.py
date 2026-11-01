#!/usr/bin/env python3
"""Compare two completed first-score replays and freeze their evidence."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys

if len(sys.argv)!=4:raise SystemExit('usage: compare_first_score.py INPUT AUTHOR PEER')
packet,author,peer=map(Path,sys.argv[1:])
assert author.resolve()!=peer.resolve() and not os.path.samefile(author/'state.json',peer/'state.json')
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
OUT=ROOT/'Computability/DiophantineConsistency/reviews/adaptive-gap85-first-score-replay'
CANTOR=ROOT/'Computability/DiophantineConsistency/reviews/adaptive-gap85-score-cantor-repair'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest=packet/'manifest.json';m=json.loads(manifest.read_text());mh=sha(manifest)
assert sha(packet/'replay.py')==m['driver_sha256'] and sha(packet/'prepare.py')==m['preparer_sha256']
assert all(sha(p)==h for p,h in m['guard'].items())
assert sha(CANTOR/'manifest.json')==m['cantor_manifest_sha256']
assert sha(CANTOR/'comparison.json')==m['cantor_comparison_sha256']
def candidates(values):
    for name,expected in values.items():
        p=Path(name)
        if expected is None:assert not os.path.lexists(p),name
        else:assert p.is_file() and str(p.resolve())==expected['resolved'] and sha(p)==expected['sha256'],name
candidates(m['candidates'])
for vals in json.loads((CANTOR/'manifest.json').read_text())['candidates'].values():candidates(vals)
states=[json.loads((p/'state.json').read_text()) for p in (author,peer)]
for root,s in zip((author,peer),states):
    assert s['status']=='PASS' and s['manifest_sha256']==mh and s['root']==str(root)
    assert set(s['direct_checks'])=={'before','after-AdaptiveGap85FirstScore','after-AdaptiveGap85FirstScoreChecks'}
    assert sha(root/'manifest.json')==mh and sha(root/'replay.py')==m['driver_sha256']
    assert sha(root/'prepare.py')==m['preparer_sha256']
    expected={name:row['resolved'] for name,row in m['selected'].items()}
    for row in s['records']:
        name=row['module'];src=root/'src/DiophantineConsistency'/(name+'.lean')
        obj=root/'lib/DiophantineConsistency'/(name+'.olean');log=root/'logs'/(name+'.log')
        assert row['exit']==0 and row['warnings']==0
        assert sha(src)==row['source_sha256'] and sha(obj)==row['object_sha256'] and sha(log)==row['log_sha256']
        assert obj.is_file() and not obj.is_symlink()
        expected[name+'.olean']=str(obj.resolve())
    assert {p.name:str(p.resolve()) for p in (root/'lib/DiophantineConsistency').iterdir()}==expected
    assert {p.name:str(p.resolve()) for p in (root/'lib').iterdir() if p.name!='DiophantineConsistency'}==m['namespace']
    for name,row in m['selected'].items():
        p=root/'lib/DiophantineConsistency'/name
        assert p.is_symlink() and sha(p)==row['sha256']
    assert [r['module'] for r in s['records']]==['AdaptiveGap85FirstScore','AdaptiveGap85FirstScoreChecks']
    assert s['records'][0]['source_sha256']==m['source_sha256'] and s['records'][1]['source_sha256']==m['checks_sha256']
assert states[0]['records']==states[1]['records']
def normalized(obj,root):
    if isinstance(obj,dict):return {k:normalized(v,root) for k,v in obj.items()}
    if isinstance(obj,list):return [normalized(v,root) for v in obj]
    return obj.replace(str(root),'<ROOT>') if isinstance(obj,str) else obj
assert normalized(states[0]['direct_checks'],author)==normalized(states[1]['direct_checks'],peer)
for row in states[0]['records']:
    name=row['module']
    for d,suffix in (('src/DiophantineConsistency','.lean'),('logs','.log')):
        assert (author/d/(name+suffix)).read_bytes()==(peer/d/(name+suffix)).read_bytes()
assert not OUT.exists(),str(OUT)
OUT.mkdir()
for label,root in (('author',author),('peer',peer)):
    dest=OUT/label;dest.mkdir()
    shutil.copyfile(root/'state.json',dest/'state.json')
    for sub in ('logs','src'):(dest/sub).mkdir()
    for row in states[0]['records']:
        name=row['module']
        shutil.copyfile(root/'src/DiophantineConsistency'/(name+'.lean'),dest/'src'/(name+'.lean'))
        shutil.copyfile(root/'logs'/(name+'.log'),dest/'logs'/(name+'.log'))
receipt={'status':'MATCHED_PASS','author':str(author),'peer':str(peer),'manifest_sha256':mh,
         'author_state_sha256':sha(author/'state.json'),'peer_state_sha256':sha(peer/'state.json'),
         'records':states[0]['records'],'direct_checks':normalized(states[0]['direct_checks'],author),
         'shared_entries':m['shared_entries'],'selected_entries':len(m['selected']),
         'parent_candidates':len(m['candidates']),'cantor_candidates':sum(len(v) for v in json.loads((CANTOR/'manifest.json').read_text())['candidates'].values()),
         'compare_sha256':sha(__file__),'scope':m['scope']}
(OUT/'comparison.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
shutil.copyfile(__file__,OUT/'compare.py')
print('MATCHED_PASS',len(receipt['records']),'rows;',receipt['shared_entries'],'shared entries;',receipt['parent_candidates'],'parent candidates',flush=True)
