#!/usr/bin/env python3
"""Small independent check of the shared unbounded-register invariant.

Mask bit i records r_i>0. Positive decrement has two abstract outcomes;
this is an overapproximation of every natural register value, not sampling.
"""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
if not __debug__:raise RuntimeError('Assertions required')
oldbytes=(ROOT/'referenceCS/pa194CS.instructions.json').read_bytes()
assert hashlib.sha256(oldbytes).hexdigest()=='e2f74c0fad95734738788b98e76dc3e11748c0819ad7ef2b2998f81e0140da87'
old=json.loads(oldbytes);new=json.loads((ROOT/'machine_csz/pa194CSZ.instructions.json').read_text())
assert len(old)==len(new)==3646
assert [i for i in range(len(old))if old[i]!=new[i]]==[26]
assert old[26]==['jump',34] and new[26]==['dec',6,34,27]
pairs=json.loads((ROOT/'machine_csz/positivity_pairs.json').read_text())
R={tuple(p)for p in pairs};assert len(R)==len(pairs)==263180 and (25,1) in R
def successors(program,pc,m):
    a=program[pc]
    if a[0]=='halt':return set()
    if a[0]=='jump':return {(a[1],m)}
    bit=1<<a[1]
    if a[0]=='inc':return {(a[2],m|bit)}
    assert a[0]=='dec'
    return {(a[3],m),(a[3],m&~bit)}if m&bit else {(a[2],m)}
for p,m in R:
    assert 0<=p<len(old) and 0<=m<512
    left,right=successors(old,p,m),successors(new,p,m)
    assert left==right and left<=R
masks=sorted(m for p,m in R if p==26)
assert len(masks)==32 and all(not(m&64)for m in masks)
assert masks==[m for m in range(512)if m&1 and not(m&(8|64|128))]
print(json.dumps({'status':'PASS','inductive_pairs':len(R),'seed':[25,1],
 'source26_masks':masks,'r6_zero_at_source26':True,'same_abstract_successors':True,
 'unbounded_register_scope':True,'kernel_checked':False},indent=2))
