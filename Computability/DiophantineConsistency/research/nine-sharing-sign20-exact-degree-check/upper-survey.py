#!/usr/bin/env python3
"""Authenticate the upper-bound provider and compare its overlay with lower."""
import hashlib
import json
import os
from pathlib import Path

P=Path(__file__).resolve().parent
D=P.parents[1]
BASE=Path('/tmp/nine-sharing-sign20-count-lower-20261110')
UPPER=Path('/tmp/nine-sharing-sign20-degree-upper-20261109')
PACKET=D/'research/nine-sharing-sign20-degree-upper-check/attempt01'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(PACKET/'state.json')=='4a482d908263106fa862e64df438f341a96cdaa2a408168d5ed6208c3ced691f'
assert sha(PACKET/'outer-result.json')=='1faeb5e81057fd269588ac12a5ac968c177e1ae9efa7d61ff955e29236975e3b'
assert sha(D/'reviews/nine-sharing-sign20-degree-upper-terminal-independent/check.py')=='da467ab42529036da431f7b21e6d71b6db5b295d6ecae9fdd87342ab593605fc'
s=json.loads((PACKET/'state.json').read_text()); outer=json.loads((PACKET/'outer-result.json').read_text())
assert s['status']=='PASS' and outer['outer_exit_code']==0
assert [r['module'] for r in s['rows']]==['Sign20SyntaxDegree','Sign20DegreeStructural','Sign20DegreeResiduals','Sign20DegreeCompose']
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
assert overlap==1455
print(json.dumps({'status':'PASS','objects':objects,'overlay_overlap':overlap,
                  'scope':'upper producer and byte-matched base overlay; deeper ancestry inherited'},sort_keys=True))
