#!/usr/bin/env python3
"""Prototype prefix-right-shifting decrement, checked by literal full steps.

The root dispatcher and PC marker are fixed. A successful decrement grows the
header gap by one, decreases its selected register, and leaves the spare suffix
unchanged. This changes the former box boundary, so the old box oracle cannot
certify it. No blank-start or general theorem follows from these samples.
"""
from pathlib import Path
from collections import Counter
import json,time
import mp_protocol_runtime as m

HERE=Path(__file__).resolve().parent
PERM=(0,2,6,8,7,5,3,1,4)

def generate():
    m.generate()
    table=m.audit.read_table((HERE.parent/'bootstrap/mp_rebased252.tm').read_bytes())
    table.update({
        (75,1):(1,'L',85),
        (85,0):(0,'L',85),(85,1):(1,'L',97),
        (97,0):(0,'L',112),(97,1):(1,'L',97),
        (112,0):(0,'R',131),(112,1):(1,'L',97),
        (131,0):(0,'R',95),
    })
    return table

def cases():
    for p,op,r in m.a.sites:
        if op!='CD':continue
        physical=PERM[r]
        for j,regs in enumerate(([1]*9,[i%3 for i in range(9)],[5,0,1,0,2,0,3,0,4])):
            regs=list(regs);regs[physical]=max(1,regs[physical])
            for gap,spares in ((40,[]),(45,[0]*2),(41,[2,0,1])):
                yield p,physical,regs,gap,spares

def run(table,case,fuel=10000,trace=False,original=False):
    p,r,regs,gap,spares=case
    q,h,ones=96,0,m.audit.paint(p,gap,regs,spares,0)
    nxt=m.audit.successor(p,'CD',r,False)
    outhead=-(nxt is None);outgap=gap+(not original)+(nxt is None)
    newregs=regs.copy();newregs[r]-=1
    target=m.audit.paint('' if nxt is None else nxt,outgap,newregs,spares+([0] if original else []),outhead)
    rows=Counter();history=[];intermediate=0;last_dispatch=None
    for step in range(1,fuel+1):
        row=q,int(h in ones);rows[row]+=1
        if row not in table:return dict(passed=False,reason='missing row',step=step,row=row),rows
        if trace:history.append([q,h,row[1]])
        w,d,q=table[row]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
        if q==254:return dict(passed=False,reason='halt',step=step),rows
        if q==96:
            if h==outhead and ones==target:
                return dict(passed=True,steps=step,intermediate_dispatches=intermediate,trace=history if trace else None),rows
            intermediate+=1
            last_dispatch=dict(steps=step,actual_head=h,expected_head=outhead,
                               extra_ones=sorted(ones-target),missing_ones=sorted(target-ones))
    return dict(passed=False,reason='fuel',steps=fuel,state=q,head=h,
                intermediate_dispatches=intermediate,last_dispatch=last_dispatch,
                trace=history if trace else None),rows

def main():
    begun=time.monotonic();table=generate()
    control=m.audit.read_table((HERE.parent/'bootstrap/mp_rebased252.tm').read_bytes())
    for case in list(cases())[:9]:
        control_result,_=run(control,case,original=True)
        assert control_result['passed'],('baseline',case,control_result)
    used=Counter();failures=[];passed=0
    for i,case in enumerate(cases()):
        result,rows=run(table,case)
        if not result['passed']:
            result,rows=run(table,case,trace=True)
            failures.append(dict(index=i,case=case,result=result));break
        used.update(rows);passed+=1
    result=dict(scope=__doc__,passed=not failures,cases_passed=passed,failures=failures,
                total_seconds=time.monotonic()-begun,working_states=len(table)//2,
                used_rows=[[q,b,n] for (q,b),n in sorted(used.items())])
    (HERE/'prefix_decrement_results.json').write_text(json.dumps(result,indent=2)+'\n')
    (HERE/'prefix_decrement252.tm').write_bytes(m.audit.encode(table))
    print(json.dumps({k:v for k,v in result.items() if k not in ('failures','used_rows','scope')},indent=2))
    if failures:print(json.dumps({k:v for k,v in failures[0]['result'].items() if k!='trace'},indent=2))

if __name__=='__main__':main()
