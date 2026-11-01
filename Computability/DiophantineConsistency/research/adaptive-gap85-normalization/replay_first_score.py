#!/usr/bin/env python3
"""Replay first-score proof over the frozen, audited two-provider union."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

D=Path(__file__).resolve().parent
M=D/'manifest.json'
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
CANTOR=ROOT/'Computability/DiophantineConsistency/reviews/adaptive-gap85-score-cantor-repair'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.olean.hash',
          '.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
raw=M.read_bytes();m=json.loads(raw);mh=hashlib.sha256(raw).hexdigest()
assert len(sys.argv)==2 and sys.argv[1]==mh and sha(__file__)==m['driver_sha256']
assert sha(D/'prepare.py')==m['preparer_sha256'] and sha(LEAN)==m['lean_sha256']
parents=[Path(m['score_parent']),Path(m['third_parent'])]
assert all(sha(p/'state.json')==h for p,h in zip(parents,m['parent_states']))
cm=json.loads((CANTOR/'manifest.json').read_text())
assert sha(CANTOR/'manifest.json')==m['cantor_manifest_sha256']
assert sha(CANTOR/'comparison.json')==m['cantor_comparison_sha256']
def candidates(values):
    for name,expected in values.items():
        p=Path(name)
        if expected is None:assert not os.path.lexists(p),name
        else:assert p.is_file() and str(p.resolve())==expected['resolved'] and sha(p)==expected['sha256'],name
def parent_audit():
    assert sha(M)==mh and sha(__file__)==m['driver_sha256'] and sha(D/'prepare.py')==m['preparer_sha256']
    assert sha(LEAN)==m['lean_sha256']
    assert all(sha(p)==h for p,h in m['guard'].items())
    assert all(sha(p/'state.json')==h for p,h in zip(parents,m['parent_states']))
    assert sha(CANTOR/'manifest.json')==m['cantor_manifest_sha256']
    assert sha(CANTOR/'comparison.json')==m['cantor_comparison_sha256']
    candidates(m['candidates'])
    for vals in cm['candidates'].values():candidates(vals)
    for i,root in enumerate(parents):
        path=root/'lib/DiophantineConsistency'
        actual={p.name:{'resolved':str(p.resolve()),'sha256':sha(p)} for p in path.iterdir() if p.is_file()}
        assert actual==m['parent_entries'][i]
    assert {p.name:str(p.resolve()) for p in (parents[0]/'lib').iterdir()
            if p.name!='DiophantineConsistency'}==m['namespace']

parent_audit()
w=Path(tempfile.mkdtemp(prefix='gap85-first-score-replay-'))
src=w/'src';lib=w/'lib';logs=w/'logs'
for p in (src/'DiophantineConsistency',lib/'DiophantineConsistency',logs):p.mkdir(parents=True,exist_ok=True)
for name,target in m['namespace'].items():(lib/name).symlink_to(target,target_is_directory=True)
for name,row in m['selected'].items():(lib/'DiophantineConsistency'/name).symlink_to(row['resolved'])
names=['AdaptiveGap85FirstScore','AdaptiveGap85FirstScoreChecks']
for name in names:shutil.copyfile(D/'sources/DiophantineConsistency'/(name+'.lean'),src/'DiophantineConsistency'/(name+'.lean'))
(w/'manifest.json').write_bytes(raw);shutil.copyfile(__file__,w/'replay.py');shutil.copyfile(D/'prepare.py',w/'prepare.py')
env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*m['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
state={'status':'RUNNING','root':str(w),'manifest_sha256':mh,'records':[],'direct_checks':{},'scope':m['scope']}
def save():(w/'state.json').write_text(json.dumps(state,sort_keys=True,indent=2)+'\n')
def overlay_audit():
    assert {p.name:str(p.resolve()) for p in lib.iterdir() if p.name!='DiophantineConsistency'}==m['namespace']
    expected={name:row['resolved'] for name,row in m['selected'].items()}
    for row in state['records']:
        if row['exit']==0:expected[row['module']+'.olean']=str((lib/'DiophantineConsistency'/(row['module']+'.olean')).absolute())
    actual={p.name:str(p.resolve()) for p in (lib/'DiophantineConsistency').iterdir()}
    assert actual==expected
    for name,row in m['selected'].items():
        p=lib/'DiophantineConsistency'/name
        assert p.is_symlink() and sha(p)==row['sha256']
    for row in state['records']:
        p=lib/'DiophantineConsistency'/(row['module']+'.olean')
        assert p.is_file() and not p.is_symlink() and sha(p)==row['object_sha256']
        assert sha(logs/(row['module']+'.log'))==row['log_sha256']
    for name,digest in zip(names,(m['source_sha256'],m['checks_sha256'])):
        p=src/'DiophantineConsistency'/(name+'.lean')
        assert p.is_file() and not p.is_symlink() and sha(p)==digest
    assert sha(w/'manifest.json')==mh and sha(w/'replay.py')==m['driver_sha256'] and sha(w/'prepare.py')==m['preparer_sha256']
def deps(stage):
    results={}
    for name in names:
        source=src/'DiophantineConsistency'/(name+'.lean')
        proc=subprocess.run([str(LEAN),'--root='+str(src),'--deps',str(source)],cwd=ROOT,env=env,capture_output=True,text=True,check=True)
        paths={str(Path(line).resolve()) for line in proc.stdout.splitlines()}
        init=str((LEAN.parent.parent/'lib/lean/Init.olean').resolve())
        if name==names[0]:
            expected={init,m['selected']['AdaptiveGap85ScoreCoding.olean']['resolved'],
                      m['selected']['AdaptiveGap85ThirdMinimal.olean']['resolved']}
        else:expected={init,str((lib/'DiophantineConsistency/AdaptiveGap85FirstScore.olean').resolve())}
        assert paths==expected,(stage,name,paths,expected)
        results[name]={'stdout':proc.stdout,'resolved':sorted(paths)}
    state['direct_checks'][stage]=results
def audit(stage):
    parent_audit();overlay_audit();deps(stage);save()
save();print('ROOT',w,flush=True)
try:
    audit('before')
    for name in names:
        source=src/'DiophantineConsistency'/(name+'.lean');obj=lib/'DiophantineConsistency'/(name+'.olean');log=logs/(name+'.log')
        with log.open('w') as out:
            r=subprocess.run([str(LEAN),'-M6000','-j1','-DElab.async=false','--root='+str(src),str(source),'-o',str(obj)],
                             cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT)
        content=log.read_text()
        row={'module':name,'exit':r.returncode,'source_sha256':sha(source),'object_sha256':sha(obj) if obj.exists() else None,
             'log_sha256':sha(log),'warnings':content.count('warning:')}
        state['records'].append(row);save();print(name,r.returncode,flush=True)
        assert r.returncode==0 and not row['warnings'] and 'error:' not in content and 'sorryAx' not in content
        if name==names[1]:
            blocks=re.findall(r'depends on axioms:\s*\[([^]]*)\]',content,re.S)
            assert len(blocks)==3 and all(not ({a.strip() for a in b.split(',') if a.strip()}-
                   {'propext','Classical.choice','Quot.sound'}) for b in blocks),(content,blocks)
        audit('after-'+name)
    state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as exc:
    state.update(status='FAILED',failure=repr(exc));save();raise
