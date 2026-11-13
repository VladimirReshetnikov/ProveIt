#!/usr/bin/env python3
"""Pure no-Lean tests of exact-path dependency multiplicity."""
import importlib.util
import json
from pathlib import Path
if not __debug__:raise SystemExit('refusing optimized Python')
p=Path(__file__).resolve().parent;spec=importlib.util.spec_from_file_location('v3_deps_test',p/'deps.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
init='/package/Init.olean';tile='/project/Tile.olean';direct={'Init':{'path':init},'Tile':{'path':tile}}
results={}
assert m.validate([init,tile],direct)=={'Init':1,'Tile':1}
assert m.validate([init,init,tile],direct)=={'Init':2,'Tile':1}
results['one_or_two_identical_init_allowed']=True

def reject(label,fn):
    try:fn()
    except ValueError as e:results[label]=repr(e)
    else:raise AssertionError('unexpected acceptance '+label)
reject('third_init',lambda:m.validate([init,init,init,tile],direct))
reject('duplicate_non_init',lambda:m.validate([init,tile,tile],direct))
reject('unrecorded_alternate_init',lambda:m.validate([init,'/toolchain/Init.olean',tile],direct))
reject('missing_direct',lambda:m.validate([init,init],direct))
counts={};assert not m.duplicate({},counts,'Init',init)
reject('alternate_init_same_module',lambda:m.duplicate(direct,counts,'Init','/toolchain/Init.olean'))
# A distinct symlink spelling must be rejected even if it might resolve to the same object.
reject('alternate_symlink_spelling',lambda:m.duplicate(direct,counts,'Init','/package/link/../Init.olean'))
assert m.validate((p.parents[1]/'reviews/current14-extension-v2-failure/first-deps.stdout').read_text().splitlines(),
    {'Init':{'path':'/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Init.olean'},
     'DiophantineConsistency.WangTiles942TableData':{'path':'/tmp/current14-printed-port-extension-20261104/lib/DiophantineConsistency/WangTiles942TableData.olean'},
     'DiophantineConsistency.WangTiles942Data':{'path':'/tmp/current14-printed-port-extension-20261104/lib/DiophantineConsistency/WangTiles942Data.olean'},
     'Mathlib.Tactic':{'path':'/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Mathlib/Tactic.olean'}})['Init']==2
results['captured_v2_first_deps_accepted_without_modification']=True
print(json.dumps({'status':'PASS','controls':results,'scope':'Pure in-memory tests only; no Lean.'},sort_keys=True))
