#!/usr/bin/env python3
"""Authenticate the staged-syntax provider and compare its overlay with lower."""
import hashlib
import json
import os
from pathlib import Path

P=Path(__file__).resolve().parent
D=P.parents[1]
BASE=Path('/tmp/nine-sharing-sign17-concrete-root-retry-20261110')
UPPER=Path('/tmp/nine-sharing-sign17-staged-syntax-check-20261110')
PACKET=D/'research/nine-sharing-sign17-staged-syntax-check/attempt01'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(PACKET/'state.json')=='dbb6e7487ac9e8f85540ccb4e1e784f194401562ecb2b937feba8c60c43a313c'
assert sha(PACKET/'outer-result.json')=='94d0fd1718b95bcd5f20cb543835ec0e765ac0edd721c63c172db169572801d6'
assert sha(D/'reviews/nine-sharing-sign17-staged-syntax-terminal-independent/check.py')=='c5f9c82d8c8d8ada75c848532301f1a199090aefb25c1f4aa622651b2ed8eedf'
s=json.loads((PACKET/'state.json').read_text()); outer=json.loads((PACKET/'outer-result.json').read_text())
assert s['status']=='PASS' and outer['author_observed_numeric_outer_exit']==0
assert [r['module'] for r in s['rows']]==[f'SharingSeed17Shared{i:02d}' for i in range(7)]+[f'SharingSeed17Row{i:02d}' for i in range(8)]+['SharingSeed17Degree96','SharingSign17Squares']
objects={}
for r in s['rows']:
    n=r['module']; src=UPPER/'src/DiophantineConsistency'/(n+'.lean'); obj=UPPER/'lib/DiophantineConsistency'/(n+'.olean')
    assert r['deps']['exit']==r['compile']['exit']==0
    assert sha(src)==r['source_sha256'] and sha(obj)==r['object_sha256']
    for kind in ('deps','compile'):
        assert sha(UPPER/(n+'-'+kind+'.txt'))==r[kind]['log_sha256']
    for path,rec in r['direct_guard'].items():
        q=Path(path)
        if rec is None: assert not os.path.lexists(q)
        else: assert q.is_file() and str(q.resolve())==rec['realpath'] and sha(q)==rec['sha256']
    assert (BASE/'lib/DiophantineConsistency'/(n+'.olean')).is_symlink() and (BASE/'lib/DiophantineConsistency'/(n+'.olean')).resolve()==obj.resolve() and sha(BASE/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
    for fallback in (Path('/tmp/current2011-spheres-fresh-base-priority-check02'),
                     Path('/tmp/normalized106-fresh-model-client-20261105'),
                     Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),
                     Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')):
        assert not os.path.lexists(fallback/'DiophantineConsistency'/(n+'.olean'))
    objects[n]={'sha256':r['object_sha256'],'realpath':str(obj.resolve())}
overlap=0
for path,dest in s['overlay_links'].items():
    q=Path(path); assert q.is_symlink() and str(q.resolve())==dest
    rel=q.relative_to(UPPER/'lib'); b=BASE/'lib'/rel
    assert b.is_file() and sha(b)==sha(q), ('missing or conflicting overlay',str(rel))
    overlap+=1
assert overlap==1057
print(json.dumps({'status':'PASS','objects':objects,'overlay_overlap':overlap,
                  'scope':'staged-syntax producer and byte-matched base overlay; deeper ancestry inherited'},sort_keys=True))
