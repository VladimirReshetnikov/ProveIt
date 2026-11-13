#!/usr/bin/env python3
"""Read-only review of the generic free-main positivity receipt."""
import hashlib
import json
import os
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent
TASK=HERE.parent.parent
PACK=TASK/'research/p64-qcube72-forward-model-guarded'
SOURCE=PACK/'FreeMainForward.lean';RUNNER=PACK/'check.py';HELPER=PACK/'missing_child.py'
OBS=PACK/'observations/attempt01';RESULT=OBS/'result.json';LOG=OBS/'compile.log'
PINS={SOURCE:'a276feac4781c3e2436f2d476b80afa0809e7509f645a35c656c8e055a078be2',
      RUNNER:'2995eb8b6ce0ce6b62c7987f1962a1e4ad55d90bbb8a39e612f2fcbec8aea271',
      HELPER:'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
      RESULT:'140647b587bbdf333631a7038ce0e9e51b59520a632b3e916b3befad82100227',
      LOG:'9856f5be4178a5e1add1d51d0dee999943083067540bfcade114714699d6c793'}
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
for p,h in PINS.items():
    if sha(p)!=h:raise RuntimeError('pin mismatch '+str(p))
x=json.loads(RESULT.read_text())
assert x['status']=='PASS' and x['exit']==0 and x['stop_reason'] is None and x['guards_stable']
assert x['guards_before']==x['guards_after'] and x['runner_sha256']==PINS[RUNNER] and x['missing_child_helper_sha256']==PINS[HELPER]
assert x['log_sha256']==PINS[LOG] and x['group_rss_samples']>=1
assert x['sampled_peak_group_rss_bytes']<x['sampled_group_rss_limit_bytes']
assert x['minimum_memavailable_bytes']>=x['min_required_memavailable_bytes']
expected=''.join("'FreeMainForward."+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
                 for name in ('root_above_base','positive_of_alignment','positive_of_pell_bound'))
assert LOG.read_text()==expected
for path,entry in x['guards_before'].items():
    p=Path(path)
    if entry is None:assert not os.path.lexists(p)
    else:assert p.is_file() and str(p.resolve())==entry['realpath'] and sha(p)==entry['sha256']
paths=[Path(p)/'IndependentYBounds.olean' for p in x['lean_path'].split(':') if p]
selected=next((p for p in paths if p.is_file()),None)
assert str(selected)=='/tmp/p64-qcube76y-bounds-priority-check03/IndependentYBounds.olean'
assert sha(selected)=='6458991845eba747546b4d45c454a31a907e226a98fbb7301d6cf30ae41da582'
assert x['guards_before'][str(selected)]['sha256']==sha(selected)
obj=Path(x['command'][x['command'].index('-o')+1])
assert obj.is_file() and not obj.is_symlink() and sha(obj)==x['object_sha256']=='52e5fd328a5a3e39abfcf7783ce59565524df2ff34c25c6fbe7d330bfb2eb0da'
chain=json.loads((TASK/'reviews/p64-qcube76y-chain-receipt-independent/result.json').read_text())
bounds=next(row for row in chain['stages'] if row['stage']=='bounds')
assert chain['status']=='PASS' and bounds['object']['path']==str(selected) and bounds['object']['sha256']==sha(selected)
print(json.dumps({'status':'PASS_RECEIPT_REVIEW','source_sha256':PINS[SOURCE],'receipt_sha256':PINS[RESULT],
                  'log_sha256':PINS[LOG],'output_sha256':x['object_sha256'],'selected_bounds_sha256':sha(selected),
                  'samples':x['group_rss_samples'],'sampled_peak_group_rss_bytes':x['sampled_peak_group_rss_bytes'],
                  'minimum_memavailable_bytes':x['minimum_memavailable_bytes'],
                  'scope':'Current direct guards and retained sampled receipt only; no Lean rerun, actual-graph hypothesis bridge, reverse map, or transitive ancestry.'},indent=2,sort_keys=True))
