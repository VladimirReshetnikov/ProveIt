#!/usr/bin/env python3
"""Reconstruct the exact 52-module policy from the pinned author manifest."""
import hashlib,json
from pathlib import Path
if not __debug__: raise RuntimeError('optimized Python is unsupported')
D=Path(__file__).resolve().parent
source=D.parent/'author-additions.json'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='081e343d107f6ff1e73b1bfded119dd3698f363169ae24c25a07b60ddff33a0d'
m=json.loads(source.read_text());order=m['order'];reports={n:m['axiom_reports'].get(n,[]) for n in order}
assert len(order)==52 and sum(map(len,reports.values()))==127 and order[-1]=='DiophantineConsistency.IPRAStandardAQ16'
policy={'addition_order':order,'expected_axiom_by_module':reports,'expected_axiom_names':reports[order[-1]],'sources':m['sources'],'target':order[-1]}
raw=(json.dumps(policy,indent=2,sort_keys=True)+'\n').encode()
assert hashlib.sha256(raw).hexdigest()=='6a9ed8f9b512752d5a9bfc6589bf093b58ab1e34b900112c082561f0567d5daa'
out=D/'task-policy.json'
if out.exists(): assert out.read_bytes()==raw
else: out.write_bytes(raw)
print('PASS_AQ16_POLICY_RECONSTRUCTION',hashlib.sha256(raw).hexdigest())
