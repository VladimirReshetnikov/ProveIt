"""Reproduce the CI0111 counterexample to an unconditional 48/131 fold.

The proposed three-step identity is valid when state48 scans0 with0 on
its left.  The complete controller does not maintain that premise.
This script is a literal finite counterexample, not a claimed reduction.
Set ZFC246_BASE to the pristine context246 archive directory.
"""
from pathlib import Path
import json
from search_tail import T, BASE, BASE_SHA256
import check_literal_instructions as c

HERE=Path(__file__).resolve().parent

def step(table,q,h,one):
    w,d,nq=table[q,int(h in one)]
    one=set(one)
    if w:one.add(h)
    else:one.discard(h)
    return nq,h+d,one

def plain(conf):
    q,h,one=conf
    return dict(state=q,head=h,ones=sorted(one))

def main():
    assert ('0111','CI',0) in c.program_sites(BASE/'sources/Prog254.v')
    regs=[0]*9
    target=c.expected('0111','CI',0,regs,[0],0,40)
    q,h,one=96,0,c.paint('0111',40,regs,[0],0)
    witness=None
    for elapsed in range(10000):
        if q==48 and h not in one and h-1 in one and witness is None:
            witness=(elapsed,(q,h,one.copy()))
        q,h,one=step(T,q,h,one)
        if (q,h,one)==(96,target[0],target[1]):break
    else:raise AssertionError('baseline did not finish')
    assert witness is not None
    n,conf=witness
    assert (n,conf[0],conf[1])==(362,48,4)
    old=step(T,*conf)
    changed=T.copy()
    changed[48,0]=(1,-1,131)
    changed[131,0]=(0,1,7)
    new=conf
    trace=[plain(new)]
    for _ in range(3):
        new=step(changed,*new)
        trace.append(plain(new))
    assert new!=old

    # All four assignments to the untouched local outer cells exhibit
    # the three-step identity when its stated left-neighbor premise holds.
    checked=[]
    for a in (0,1):
        for b in (0,1):
            local={-8,11}|({-2} if a else set())|({1} if b else set())
            start=(48,0,local)
            old_local=step(T,*start)
            new_local=start
            for _ in range(3):new_local=step(changed,*new_local)
            assert new_local==old_local
            checked.append([a,b])

    result=dict(status='literal_counterexample_to_unconditional_fold',baseline_sha256=BASE_SHA256,
        source_instruction=dict(pc='0111',kind='CI',logical_register=0),
        frame=dict(primary_registers=regs,spares=[0],head=0,span=40),
        baseline_instruction_steps=elapsed+1,witness_after_steps=n,witness=plain(conf),
        patch=[[48,0,1,-1,131],[131,0,0,1,7]],
        baseline_after_one_step=plain(old),patched_three_step_trace=trace,
        disproved_premise='Every normal return at state48 reading0 has0 immediately to its left.',
        valid_conditional_identity='If cells h and h-1 are both0, patched48 takes3 steps to exactly the old48/0 one-step endpoint; all other cells are untouched.',
        conditional_identity_local_checks=checked,
        limitation='This counterexample rejects the unconditional local identity. It does not by itself prove that every larger coordinated redesign using these rows is invalid.')
    path=HERE/'return-counterexample.json'
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(output=path.name,witness_after_steps=n,state=conf[0],head=conf[1],
        baseline_instruction_steps=elapsed+1,baseline_endpoint=[old[0],old[1]],patched_endpoint=[new[0],new[1]])))

if __name__=='__main__':main()
