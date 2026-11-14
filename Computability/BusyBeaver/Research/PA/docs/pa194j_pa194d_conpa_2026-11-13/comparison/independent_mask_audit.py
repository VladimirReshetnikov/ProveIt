#!/usr/bin/env python3
"""Independent finite inductive-invariant audit of a zero-jump source rewrite.

A set bit says a natural register is positive. On a positive decrement the
successor bit is either0 or1, an intentional sound overapproximation.
The checker imports no construction code and recomputes the reachable closure.
"""
import argparse,collections,hashlib,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--parent',type=Path,required=True);ap.add_argument('--child',type=Path,required=True);ap.add_argument('--masks',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
p=json.loads(a.parent.read_text());c=json.loads(a.child.read_text());saved=json.loads(a.masks.read_text())
assert len(p)==len(c)==3646
S={(int(i),m)for i,ms in saved.items()for m in ms}
assert all(0<=i<len(p) and 0<=m<512 for i,m in S)

def successors(instructions,pc,mask):
    row=instructions[pc];op=row[0]
    if op=='jump':return {(row[1],mask)}
    if op=='inc':return {(row[2],mask|2**row[1])}
    if op=='halt':return set()
    assert op=='dec' and len(row)==4
    reg,z,n=row[1:];bit=2**reg
    if mask&bit:return {(n,mask),(n,mask-bit)}
    return {(z,mask)}

seed=(25,1)
assert seed in S
queue=collections.deque([seed]);reachable={seed}
while queue:
    q,m=queue.popleft()
    for nxt in successors(p,q,m):
        assert 0<=nxt[0]<len(p) and 0<=nxt[1]<512
        if nxt not in reachable:reachable.add(nxt);queue.append(nxt)
assert reachable==S
changes=[i for i in range(len(p))if p[i]!=c[i]]
assert changes==[3,9,26,3526,3532,3544,3550,3553,3627,3633]
evidence=[]
for i in changes:
    assert p[i][0]=='jump' and c[i][0]=='dec' and c[i][2]==p[i][1] and c[i][3]==i+1
    reg=c[i][1];ms=sorted(m for j,m in S if j==i)
    assert ms and all((m&2**reg)==0 for m in ms)
    evidence.append({'ordinal':i,'register_proved_zero':reg,'reachable_masks_at_site':len(ms),'old_jump_target':p[i][1],'new_zero_branch_target':c[i][2],'unused_positive_branch_target':c[i][3]})
for i,m in S:
    ps=successors(p,i,m);cs=successors(c,i,m)
    assert ps==cs
    assert ps<=S
out={'scope':'Fresh independent least abstract reachability computation and source identity under the resulting invariant; imports no builder/compiler/runtime code. Proof of concretization soundness is the elementary natural-register case analysis stated in the report.','seed_source_ordinal':25,'seed_positivity_mask':1,'seed_logical_registers':[2,0,0,0,0,0,0,0,0],'pairs':len(S),'source_sites_with_some_mask':len({i for i,m in S}),'recomputed_least_closure_equals_saved_set':True,'both_source_successors_agree_at_every_pair':True,'both_source_abstract_successors_stay_inside_set':True,'all_ten_new_tests_always_take_zero_branch':True,'changed_sites':evidence,'parent_instructions_sha256':hashlib.sha256(a.parent.read_bytes()).hexdigest(),'child_instructions_sha256':hashlib.sha256(a.child.read_bytes()).hexdigest(),'mask_file_sha256':hashlib.sha256(a.masks.read_bytes()).hexdigest()}
a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
