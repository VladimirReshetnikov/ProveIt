#!/usr/bin/env python3
"""Reproduce the concrete wrong branch in the unsafe shared-scanner250 table.

This is a rejection artifact, not a proposed consistency machine. The source
decrement sees zero and must skip its enclosing zero-test branch. The250 table
instead takes the nonzero successor while leaving the register zero.
"""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
PC='1110100100100000100'
ZERO_PC='111010010010000011'
WRONG_PC='1110100100100000101'

def parse(path):
    table={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();table[int(q),int(b)]=int(w),d,int(t)
    return table

def paint(pc,gap):
    ones={-1,gap}|{i for i,b in enumerate(pc) if b=='1'}
    ones|={gap+2+2*r for r in range(9)}
    return ones

def run(table,target):
    q,h,ones=96,0,paint(PC,43);restore=None
    for step in range(10001):
        if q==0 and h not in ones and restore is None:
            restore=dict(step=step,state=q,head=h,ones=sorted(ones))
        if step and(q,h)==(96,0)and ones==target:
            return dict(steps=step,restore_entry=restore,
                        steps_after_restore=step-restore['step'],state=q,head=h,
                        ones=sorted(ones))
        assert q!=254,('unexpected halt',step)
        w,d,q=table[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R'else-1
    raise AssertionError('specific exact outcome not reached within10000 steps')

def main():
    original=HERE/'prefix_decrement252.tm'
    unsafe=HERE.parent/'compression/prefix_zero250.tm'
    baseline=parse(original);table=parse(unsafe)
    redirected={k:(w,d,{112:3,97:1}.get(t,t)) for k,(w,d,t) in baseline.items() if k[0] not in(112,97)}
    redirected[3,0]=0,'R',131
    assert table==redirected and len(table)==500
    good=run(baseline,paint(ZERO_PC,43))
    bad=run(table,paint(WRONG_PC,44))
    assert bad['steps_after_restore']==209
    assert bad['restore_entry']==good['restore_entry']
    result=dict(status='REJECTED_WRONG_ZERO_BRANCH',scope=__doc__,
                candidate_working_states=250,
                original_sha256=hashlib.sha256(original.read_bytes()).hexdigest(),
                candidate_sha256=hashlib.sha256(unsafe.read_bytes()).hexdigest(),
                coordinated_changes=dict(remove_states=[112,97],redirect_targets={'112':3,'97':1},
                                         replace_row=dict(state=3,read=0,before=[0,'L',48],after=[0,'R',131])),
                input=dict(state=96,head=0,pc=PC,physical_registers=[0]*9,
                           selected_physical_register=0,gap=43,spares=[]),
                required_zero_successor=dict(pc=ZERO_PC,gap=43,physical_registers=[0]*9,spares=[]),
                actual_wrong_successor=dict(pc=WRONG_PC,gap=44,physical_registers=[0]*9,spares=[]),
                correct252_execution=good,unsafe250_execution=bad)
    (HERE/'shared_scanner_counterexample.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in('scope','correct252_execution','unsafe250_execution')},indent=2))
    print('Literal root-to-root steps:252 control',good['steps'],'unsafe250',bad['steps'])

if __name__=='__main__':main()
