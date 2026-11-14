#!/usr/bin/env python3
"""Repeat the complete inherited symbolic runtime checks for PA195S8.

This checker intentionally uses the pinned symbolic runtime; it is a repeated
verification, not an independently implemented symbolic engine.
"""
import json, sys, time, hashlib
from pathlib import Path
SOURCE=Path(sys.argv[1])
BASE=Path(sys.argv[2])
OUT=Path(sys.argv[3]) if len(sys.argv)>3 else Path(__file__).resolve().parent
sys.path.insert(0,str(BASE))
import build_verify as v
start=time.time()
t=v.c.read_grammar(SOURCE/'grammar.json')
sites,cfg,contracts=v.c.source(t)
source=v.source_binding(t,sites,cfg)
emitter=v.emitter(t)
raw=v.table(SOURCE/'unfolded203.native.tm')
folded=v.table(SOURCE/'pa195_scanner8.native.tm')
result={}
for tag,rows in [('raw203',raw),('folded195',folded)]:
    r=v.c.validate(rows,contracts)
    if not r['ok']:raise ValueError((tag,r))
    result[tag]=r
    print(tag,json.dumps(r),flush=True)
receipt={'source':source,'emitter':emitter,'runtime':result,'seconds':time.time()-start,
         'symbolic_engine_independently_implemented':False,'complete_contracts_rechecked':True,
         'dense_sha256':hashlib.sha256((SOURCE/'pa195_scanner8.tm').read_bytes()).hexdigest(),
         'scope':'Repeated verification using the pinned PA195 symbolic executor and oracle premises independently audited by independent_audit_scanner8.py; not a newly kernel-checked theorem.'}
(OUT/'runtime_recheck.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
