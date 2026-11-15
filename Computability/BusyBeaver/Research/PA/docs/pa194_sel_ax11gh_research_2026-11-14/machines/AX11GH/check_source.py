#!/usr/bin/env python3
"""Bind the exact cache-only source edit to the literal five-row change."""
from pathlib import Path
import json, hashlib
import inherited_source_binding as resolve
ROOT=Path(__file__).resolve().parent

def rows(path):
    out={}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):continue
        q,b,w,d,t=line.split();out[int(q),int(b)]=(int(w),d,int(t))
    return out

def check():
    old_nodes=json.loads((ROOT/'inputs/nodes.json').read_text())
    new_nodes=json.loads((ROOT/'machine/nodes.json').read_text())
    expected=dict(old_nodes)
    expected['node170']=[['node36',['node167','node145']],'node57']
    assert new_nodes==expected
    grammar=json.loads((ROOT/'inputs/grammar.tree.json').read_text())
    assert grammar==json.loads((ROOT/'machine/grammar.tree.json').read_text())
    old_sites=resolve.flatten(grammar,old_nodes)
    new_sites=resolve.flatten(grammar,new_nodes)
    old=resolve.resolve(old_sites);new=resolve.resolve(new_sites)
    assert new_sites==json.loads((ROOT/'machine/sites.json').read_text())
    assert new==json.loads((ROOT/'machine/instructions.json').read_text())
    removed=3661
    assert len(old)==3672 and len(new)==3671
    assert old[removed]==['inc',6,3662]
    assert old[3660]==['dec',1,3663,3661]
    assert old[3662]==['jump',3660]
    def relocate(i):return i-int(i>removed)
    for i,ins in enumerate(old):
        if i==removed:continue
        k=2 if ins[0] in ('inc','dec') else 1
        assert ins[:k]+[relocate(j) for j in ins[k:]]==new[relocate(i)]
    assert new[3660:3662]==[['dec',1,3662,3661],['jump',3660]]
    oldrows=rows(ROOT/'inputs/machine.native.tm')
    newrows=rows(ROOT/'machine/machine.native.tm')
    edits=[[q,b,oldrows[q,b],newrows[q,b]] for q,b in sorted(oldrows) if oldrows[q,b]!=newrows[q,b]]
    assert {tuple(x[:2])for x in edits}=={(38,0),(38,1),(214,0),(214,1),(312,0)}
    result=dict(status='PASS',removed_site=removed,removed_instruction=old[removed],
                retained_sites=len(new),all_retained_operations_and_successors_relocated=True,
                meaning='The T-to-X transfer loop becomes a T-clear loop; the H-to-T/X copy is unchanged.',
                native_transition_edits=edits,
                dense_sha256=hashlib.sha256((ROOT/'machine/machine.tm').read_bytes()).hexdigest())
    (ROOT/'machine/source_binding.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':check()
