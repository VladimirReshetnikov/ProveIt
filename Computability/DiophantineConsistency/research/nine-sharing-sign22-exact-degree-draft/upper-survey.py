#!/usr/bin/env python3
"""Authenticate the upper-bound provider and compare its overlay with lower."""
import hashlib
import json
import os
from pathlib import Path

P=Path(__file__).resolve().parent
D=P.parents[1]
BASE=Path('/tmp/nine-sharing-sign22-full-coeff-20261109')
UPPER=Path('/tmp/nine-sharing-sign22-degree-upper-20261109')
PACKET=D/'research/nine-sharing-sign22-degree-upper-check/attempt01'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(PACKET/'state.json')=='648dde73a4b581706db89bf54f58fe7586c971f45970716ef21f82faee7d7fed'
assert sha(PACKET/'outer-result.json')=='781376e5a702d0f21548fdbc9c1a226a1caa88216601979cf7927eef15434e78'
assert sha(D/'reviews/nine-sharing-sign22-degree-upper-terminal-independent/check.py')=='9ca63996b9c8617661cf9abd7c1975de1c6464b5ac3b50864b93e254747e824a'
s=json.loads((PACKET/'state.json').read_text()); outer=json.loads((PACKET/'outer-result.json').read_text())
assert s['status']=='PASS' and outer['outer_exit_code']==0
assert [r['module'] for r in s['rows']]==['Sign22SyntaxDegree','Sign22DegreeStructural','Sign22DegreeResiduals','Sign22DegreeCompose']
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
    assert not os.path.lexists(BASE/'lib/DiophantineConsistency'/(n+'.olean'))
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
assert overlap==1426
print(json.dumps({'status':'PASS','objects':objects,'overlay_overlap':overlap,
                  'scope':'upper producer and byte-matched base overlay; deeper ancestry inherited'},sort_keys=True))
