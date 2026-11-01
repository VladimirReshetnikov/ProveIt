#!/usr/bin/env python3
"""Freeze direct inputs for a historical Cantor-object reproduction."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

D = Path(__file__).resolve().parent
ROOT = D.parents[3]
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SOURCE = ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCantor.lean'
CODE = ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean'
SCORE_DRIVER = ROOT/'Computability/DiophantineConsistency/research/adaptive-gap85-normalization/replay_score_coding.py'
SCORE_PARENT = Path('/tmp/gap85-balance-least-replay-75g18vpi')
BOUNDARY_STATE = Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl/state.json')
OLD = Path('/tmp/adaptive13-cell-root-parent-wnvsel13')
SUFFIXES = ('.olean','.olean.private','.olean.server','.ir','.ilean',
            '.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
MODULES = ('Init','Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring',
           'BusyBeaver.ZFC.Code254','BusyBeaver.ZFC.ArithmeticCantor')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
    return json.loads(Path(p).read_text())

old=read(OLD/'state.json'); parent=read(SCORE_PARENT/'state.json'); boundary=read(BOUNDARY_STATE)['boundary']
assert old['status']=='FAILED' and old['failure']=='DiophantineConsistency.ArithmeticWangTable'
assert old['records'][-1]['name']=='ArithmeticWangTable' and old['records'][-1]['exit']==137
assert parent['status']=='PASS' and len(parent['records'])==2
rows={row['name']:row for row in old['records']}
assert rows['ZFC/ArithmeticCantor']['exit']==rows['ZFC/Code254']['exit']==0
assert H(SOURCE)==rows['ZFC/ArithmeticCantor']['source_sha256']
assert H(CODE)==rows['ZFC/Code254']['source_sha256']
guard={}
for path in [LEAN,SOURCE,CODE,SCORE_DRIVER,SCORE_PARENT/'state.json',BOUNDARY_STATE,OLD/'state.json',
             OLD/'logs/BusyBeaver/ZFC/ArithmeticCantor.lean',OLD/'logs/BusyBeaver/ZFC/ArithmeticCantor.log',
             OLD/'logs/BusyBeaver/ZFC/Code254.lean',OLD/'logs/BusyBeaver/ZFC/Code254.log',D/'prepare.py',D/'replay.py']:
    guard[str(path)]=H(path)
for name in ('ArithmeticCantor','Code254'):
    row=rows['ZFC/'+name]
    assert H(OLD/'logs/BusyBeaver/ZFC'/(name+'.lean'))==row['source_sha256']
    assert H(OLD/'logs/BusyBeaver/ZFC'/(name+'.log'))==row['log_sha256']

roots=[str(SCORE_PARENT/'lib'),*boundary]
assert len(roots)==len(set(roots))
candidates={};selected={}
for module in MODULES:
    stem=module.replace('.','/')
    candidates[module]={}
    for root in roots:
        for suffix in SUFFIXES:
            p=Path(root)/(stem+suffix)
            if p.is_file():
                candidates[module][str(p)]={'sha256':H(p),'resolved':str(p.resolve())}
            else:
                assert not os.path.lexists(p), ('broken symlink',str(p))
                candidates[module][str(p)]=None
    p=next((Path(root)/(stem+'.olean') for root in roots if (Path(root)/(stem+'.olean')).is_file()),None)
    assert p is not None,module
    selected[module]={'logical':str(p),'resolved':str(p.resolve()),'sha256':H(p)}
for name in ('ArithmeticCantor','Code254'):
    module='BusyBeaver.ZFC.'+name;row=rows['ZFC/'+name]
    assert selected[module]['sha256']==row['object_sha256']
    assert selected[module]['resolved']==str((OLD/'lib/BusyBeaver/ZFC'/(name+'.olean')).resolve())
env=dict(os.environ,LEAN_PATH=':'.join(roots),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
deps=subprocess.run([str(LEAN),'--deps',str(SOURCE)],env=env,cwd=ROOT,capture_output=True,text=True,check=True)
expected=[selected[x]['logical'] for x in ('Init','Init','Foundation.FirstOrder.Arithmetic.IOpen.Basic',
                                           'Mathlib.Tactic.Ring','BusyBeaver.ZFC.Code254')]
assert deps.stdout.splitlines()==expected and not deps.stderr,(deps.stdout,deps.stderr)
for path,digest in guard.items():assert H(path)==digest,path
for module,records in candidates.items():
    for path,info in records.items():
        p=Path(path)
        if info is None:assert not os.path.lexists(p),path
        else:assert p.is_file() and str(p.resolve())==info['resolved'] and H(p)==info['sha256'],path
manifest={'schema':'score-cantor-direct-reproduction-v1','root':str(ROOT),'lean':str(LEAN),
          'source':str(SOURCE),'source_sha256':H(SOURCE),'score_parent':str(SCORE_PARENT),
          'roots':roots,'guard':guard,'candidates':candidates,'selected':selected,
          'original_provider':str(OLD),'original_provider_status':old['status'],
          'original_failure':old['failure'],'original_rows':{k:rows['ZFC/'+k] for k in ('ArithmeticCantor','Code254')},
          'deps_stdout':deps.stdout,'old_cantor_log_sha256':rows['ZFC/ArithmeticCantor']['log_sha256'],
          'expected_olean_sha256':rows['ZFC/ArithmeticCantor']['object_sha256'],
          'scope':'Direct-input reproduction only; original provider failed later, '
                  'and transitive project/package and dynamic ancestry remain inherited.'}
out=D/'manifest.json';assert not out.exists(),'refusing to overwrite manifest'
out.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print('PREPARED',H(out),'candidate_paths',sum(len(x) for x in candidates.values()))
