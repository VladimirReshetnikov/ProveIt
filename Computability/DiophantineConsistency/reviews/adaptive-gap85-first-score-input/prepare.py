#!/usr/bin/env python3
"""Freeze a guarded union of the score and third-minimal providers."""
from pathlib import Path
import hashlib
import json
import os
import shutil

ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
RESEARCH=ROOT/'Computability/DiophantineConsistency/research/adaptive-gap85-normalization'
REVIEWS=ROOT/'Computability/DiophantineConsistency/reviews'
OUT=REVIEWS/'adaptive-gap85-first-score-input'
A=Path('/tmp/gap85-score-coding-v3-fvonw8go')
B=Path('/tmp/gap85-third-minimal-replay-kifxjc45')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SCORE=REVIEWS/'adaptive-gap85-score-coding-v3-replay'
THIRD=REVIEWS/'adaptive-gap85-third-minimal-replay'
CANTOR=REVIEWS/'adaptive-gap85-score-cantor-repair'
BOUNDARY=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl/state.json')
SOURCE=RESEARCH/'AdaptiveGap85FirstScore.lean'
DRIVER=RESEARCH/'replay_first_score.py'
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.olean.hash',
          '.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text())
guard={}
def pin(path,expected=None):
    path=Path(path); assert path.is_file(),str(path)
    digest=sha(path)
    if expected is not None: assert digest==expected,(str(path),digest,expected)
    key=str(path.resolve())
    if key in guard: assert guard[key]==digest,key
    guard[key]=digest
    return digest

sa,sb=load(A/'state.json'),load(B/'state.json')
assert sa['status']==sb['status']=='PASS'
score,third=load(SCORE/'comparison.json'),load(THIRD/'comparison.json')
terminal,audit=load(SCORE/'terminal.json'),load(SCORE/'independent-audit.json')
assert score['status']==third['status']=='MATCHED_PASS' and audit['status']=='PASS'
assert score['peer']==str(A) and third['peer']==str(B)
pin(A/'state.json',score['peer_state_sha256']);pin(B/'state.json',third['peer_state_sha256'])
assert terminal['status']=='PASS_EXIT_0_OBSERVED'
assert terminal['comparison_sha256']==sha(SCORE/'comparison.json')
assert terminal['independent_audit_sha256']==sha(SCORE/'independent-audit.json')
assert all(terminal[k]['exit_code']==0 for k in ('author','peer','comparator','independent_audit'))
for root,state in ((A,sa),(B,sb)):
    for row in state['records']:
        n=row['module']
        pin(root/'src/DiophantineConsistency'/(n+'.lean'),row['source_sha256'])
        pin(root/'lib/DiophantineConsistency'/(n+'.olean'),row['object_sha256'])
        pin(root/'logs'/(n+'.log'),row['log_sha256'])
        assert row['exit']==0 and row['warnings']==0
for path,digest in sb['anchors'].items():pin(path,digest)
for path in (SOURCE,DRIVER,LEAN,BOUNDARY,SCORE/'comparison.json',SCORE/'terminal.json',
             SCORE/'independent-audit.json',THIRD/'comparison.json',
             CANTOR/'manifest.json',CANTOR/'comparison.json',CANTOR/'terminal.json'):
    pin(path)
cm,cc,ct=load(CANTOR/'manifest.json'),load(CANTOR/'comparison.json'),load(CANTOR/'terminal.json')
assert cc['status']=='MATCHED_PASS' and ct['status']=='PASS_EXIT_0_OBSERVED'
assert cc['manifest_sha256']==sha(CANTOR/'manifest.json')
assert ct['manifest_sha256']==sha(CANTOR/'manifest.json') and ct['comparison_sha256']==sha(CANTOR/'comparison.json')
assert all(ct[k]['exit_code']==0 for k in ('author','peer','comparator','independent_packet_audit'))
for path,digest in cm['guard'].items():pin(path,digest)
def check_candidates(candidates):
    for name,expected in candidates.items():
        p=Path(name)
        if expected is None:assert not os.path.lexists(p),name
        else:assert p.is_file() and str(p.resolve())==expected['resolved'] and sha(p)==expected['sha256'],name
for values in cm['candidates'].values():check_candidates(values)

entries=[]; maps=[]
for root in (A,B):
    d=root/'lib/DiophantineConsistency'
    items={p.name:p for p in d.iterdir()}
    assert all(p.is_file() for p in items.values())
    maps.append(items)
    entries.append({name:{'resolved':str(path.resolve()),'sha256':pin(path)} for name,path in sorted(items.items())})
shared=set(maps[0])&set(maps[1])
assert all(sha(maps[0][n])==sha(maps[1][n]) for n in shared), 'conflicting shared object or companion bytes'
selected={}
for index,items in enumerate(entries):
    for name,value in items.items():
        selected.setdefault(name,{'provider':index,**value})

# Record all relevant companion presences and absences in both parent
# namespaces, including the future output modules, to detect new shadowing.
stems=set()
for name in selected:
    suffix=next((s for s in sorted(SUFFIXES,key=len,reverse=True) if name.endswith(s)),None)
    assert suffix is not None,name
    stems.add(name[:-len(suffix)])
stems.update(('AdaptiveGap85FirstScore','AdaptiveGap85FirstScoreChecks'))
candidates={}
for root in (A,B):
    for stem in sorted(stems):
        for suffix in SUFFIXES:
            path=root/'lib/DiophantineConsistency'/(stem+suffix)
            if path.is_file():candidates[str(path)]={'resolved':str(path.resolve()),'sha256':pin(path)}
            else:assert not os.path.lexists(path);candidates[str(path)]=None

namespace={}
for path in sorted((A/'lib').iterdir()):
    if path.name!='DiophantineConsistency':
        assert path.is_symlink() and path.exists()
        namespace[path.name]=str(path.resolve())
for root in (A,B):
    cantor=root/'lib/BusyBeaver/ZFC/ArithmeticCantor.olean'
    assert str(cantor.resolve())==cm['selected']['BusyBeaver.ZFC.ArithmeticCantor']['resolved']
    pin(cantor,cc['object_sha256'])
assert all(sha(path)==digest for path,digest in guard.items())
check_candidates(candidates)
for values in cm['candidates'].values():check_candidates(values)
assert not OUT.exists(),str(OUT)
(OUT/'sources/DiophantineConsistency').mkdir(parents=True)
shutil.copyfile(SOURCE,OUT/'sources/DiophantineConsistency/AdaptiveGap85FirstScore.lean')
checks=('import DiophantineConsistency.AdaptiveGap85FirstScore\n'
        '#print axioms DiophantineConsistency.AdaptiveGap85FirstScore.firstScore_definable\n'
        '#print axioms DiophantineConsistency.AdaptiveGap85FirstScore.exists_first_minimizing_zero\n'
        '#print axioms DiophantineConsistency.AdaptiveGap85FirstScore.exists_first_minimal_blocked\n'
        '#check DiophantineConsistency.AdaptiveGap85FirstScore.exists_first_minimal_blocked\n')
(OUT/'sources/DiophantineConsistency/AdaptiveGap85FirstScoreChecks.lean').write_text(checks)
shutil.copyfile(DRIVER,OUT/'replay.py');shutil.copyfile(__file__,OUT/'prepare.py')
manifest={'score_parent':str(A),'third_parent':str(B),'parent_states':[sha(A/'state.json'),sha(B/'state.json')],
          'source_sha256':sha(SOURCE),'checks_sha256':sha(OUT/'sources/DiophantineConsistency/AdaptiveGap85FirstScoreChecks.lean'),
          'driver_sha256':sha(DRIVER),'preparer_sha256':sha(__file__),'lean_sha256':sha(LEAN),
          'guard':guard,'parent_entries':entries,'shared_entries':len(shared),'selected':selected,
          'candidates':candidates,'namespace':namespace,'boundary':load(BOUNDARY)['boundary'],
          'cantor_manifest_sha256':sha(CANTOR/'manifest.json'),
          'cantor_comparison_sha256':sha(CANTOR/'comparison.json'),
          'scope':'Model-theoretic first-score minimum/blocker; no 85 equivalence or iPRA derivation. '
                  'Direct provider union and Cantor gates checked; transitive project/package and dynamic ancestry inherited.'}
(OUT/'manifest.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
print('PREPARED',OUT,'shared',len(shared),'selected',len(selected),'candidate paths',len(candidates),flush=True)
