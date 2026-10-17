#!/usr/bin/env python3
"""Try a terminal-cell lookahead to restore zero branching in shared250.

After the carry109 encounters00, positive prefix-DEC has a1 immediately to
the right; zero prefix-DEC and INC encounter exterior0. One extra state checks
that bit. The latter branch must distinguish zeroDEC from INC through their
remaining PC phase, using existing return control.
"""
from pathlib import Path
import sys,json,time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'compression'))
import prefix_zero_repair as z

def cases():
    selected={}
    for pc,op,r in z.p.m.a.sites:
        if op in('CI','CD'):selected.setdefault((op,z.p.PERM[r]),pc)
    for kind in ('zero','inc','positive'):
        op='CI'if kind=='inc'else'CD'
        for r in range(9):
            pc=selected[op,r]
            for vector in ([0]*9,[i%3 for i in range(9)],[5,0,1,0,2,0,3,0,4]):
                regs=list(vector)
                if kind=='zero':regs[r]=0
                if kind=='positive':regs[r]=max(1,regs[r])
                gap=43;initial=z.audit.paint(pc,gap,regs,[],0)
                zero=kind=='zero';nxt=z.audit.successor(pc,op,r,zero);outhead=-(nxt is None)
                changed=regs.copy()
                if kind=='inc':changed[r]+=1
                if kind=='positive':changed[r]-=1
                outgap=gap+(nxt is None)+(kind=='positive')
                expected=z.audit.paint(''if nxt is None else nxt,outgap,changed,[],outhead)
                q,h,ones=96,0,initial.copy()
                for step in range(10000):
                    if step and(q,h)==(96,outhead)and ones==expected:break
                    w,d,q=z.base[q,int(h in ones)]
                    if w:ones.add(h)
                    else:ones.discard(h)
                    h+=1 if d=='R'else-1
                else:raise AssertionError(('prefix252 control failed',kind,r,pc))
                q,h,ones=96,0,initial.copy()
                for step in range(10000):
                    if q==109 and h not in ones:break
                    w,d,q=z.T[q,int(h in ones)]
                    if w:ones.add(h)
                    else:ones.discard(h)
                    h+=1 if d=='R'else-1
                else:raise AssertionError(('109 entry not reached',kind,r,pc))
                assert int(h+1 in ones)==(kind=='positive'),(kind,r)
                extras=range(3) if kind=='zero'else[(kind=='positive')]
                targets=[z.audit.paint(''if nxt is None else nxt,gap+(nxt is None)+extra,changed,[],outhead)for extra in extras]
                yield dict(kind=kind,pc=pc,r=r,registers=regs,head=h,ones=ones,
                           outhead=outhead,targets=targets)

def run(table,case,fuel=10000):
    q,h,ones=109,case['head'],case['ones'].copy()
    checkpoint=q,h,ones.copy();power=1;period=0
    for step in range(fuel):
        if q==96 and h==case['outhead']and any(ones==target for target in case['targets']):
            return dict(passed=True,steps=step)
        if q==254:return dict(passed=False,reason='halt',steps=step)
        w,d,q=table[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R'else-1;period+=1
        if (q,h)==checkpoint[:2]and ones==checkpoint[2]:return dict(passed=False,reason='cycle',steps=step+1)
        if period==power:checkpoint=q,h,ones.copy();power*=2;period=0
    return dict(passed=False,reason='fuel',steps=fuel)

def main():
    begun=time.monotonic();examples=list(cases())
    # Put one of each type early; every remaining example is still mandatory.
    order=[0,27,54]+[i for i in range(len(examples))if i not in(0,27,54)]
    table=z.T.copy();table[109,0]=(0,'R',255);table[255,1]=(1,'L',63)
    states=sorted({q for q,b in table})+[254]
    survivors=[];failures=[];near=[];checks=0
    for w in (0,1):
        for d in ('L','R'):
            for target in states:
                table[255,0]=(w,d,target)
                for j,i in enumerate(order):
                    outcome=run(table,examples[i]);checks+=1
                    if not outcome['passed']:break
                else:
                    name=f'tail_lookahead_{w}{d}{target}.tm'
                    (HERE/name).write_bytes(z.audit.encode(table));survivors.append(name)
                    print('SURVIVOR',name,flush=True);continue
                failures.append([w,d,target,i,outcome])
                if j:near.append(dict(action=[w,d,target],cases_passed=j,failure_kind=examples[i]['kind']))
    result=dict(scope=__doc__,samples=len(examples),fixed_positive_action=[1,'L',63],
                tested=len(states)*4,literal_checks=checks,survivors=survivors,near=near,
                failures=failures,seconds=time.monotonic()-begun)
    (HERE/'prefix_tail_lookahead_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k not in('failures','scope')},indent=2))

if __name__=='__main__':main()
