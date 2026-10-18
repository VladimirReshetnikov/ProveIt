#!/usr/bin/env python3
"""Independent endpoint/offset controls and full baseline relaxed replays."""
from pathlib import Path
from collections import Counter
import sys,json,time,argparse
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import workspace_affine as W
import workspace_block_affine as WB
if (HERE/'common.py').is_file():
    import common as C
else:
    import search_common as C
import source_block_affine as B

def rejected(f):
    try:f()
    except (AssertionError,KeyError):return
    raise AssertionError('negative control was accepted')

def offset_controls():
    checked=0
    for mask in range(1,32):
        atoms=[i for i in range(5) if mask&(1<<i)]
        samples=[i for i in range(4) if mask&(1<<i)]
        if mask&16:samples.extend((4,5,17,1024))
        for offset in range(-8,9):
            if min(atoms)+offset<0:
                rejected(lambda:W.offset_bounds(mask,offset));checked+=1;continue
            low,high=W.offset_bounds(mask,offset)
            assert all(low<=n+offset and (high is None or n+offset<=high) for n in samples)
            masks=(mask,)*9;effect=(offset,)*9
            got=W.oracle('95',('mark',0,effect),masks)
            if high==0:
                assert all(n+offset==0 for n in samples)
                assert got==('112',('plain',effect),0)
            elif low>0:
                assert all(n+offset>0 for n in samples)
                assert got==('48',('plain',W.shift(effect,0,-1)),1)
            else:assert got is None
            checked+=1
    # An unbounded tail translated down to zero is not a zero proof.
    assert W.oracle('95',('mark',0,(-4,)*9),(16,)*9) is None;checked+=1
    for r in range(9):
        entry=next(q for q,rr in W.SKIP.items() if rr==r)
        state=('plain',None);headers=0
        # Two increments and two positive decrements restore all primaries,
        # while appending two spares and growing the header distance by two.
        for operation in ('73','73','95','95'):
            _,marked,extra=W.oracle(entry,state,(31,)*9);assert extra==0
            q,state,extra=W.oracle(operation,marked,(31,)*9)
            assert q=='48';headers+=extra
        assert state==('plain',W.ZERO) and headers==2;checked+=1
        # From an exact one, the second CD must take its zero branch.
        _,marked,_=W.oracle(entry,('plain',None),(2,)*9)
        q,state,extra=W.oracle('95',marked,(2,)*9)
        assert q=='48' and extra==1
        _,marked,_=W.oracle(entry,state,(2,)*9)
        assert W.oracle('95',marked,(2,)*9)==('112',state,0);checked+=1
        assert W.oracle('95',('mark',r,W.ZERO),(31,)*9) is None;checked+=1
    return checked

def endpoint_controls():
    checked=0
    def frame(pc='101',gap=37,effect=W.ZERO):
        return W.canon([('b',1)],[("b",int(b)) for b in pc]+
            [('r',0,1,gap),('b',1),('box',('plain',effect))])
    for gap in (37,38,1000):
        assert W.matches(frame(gap=gap),{'101'},W.ZERO);checked+=1
    assert W.matches(frame(pc='10100',gap=35),{'101'},W.ZERO);checked+=1
    assert W.matches(frame(effect=None),{'101'},W.ZERO);checked+=1
    assert not W.matches(frame(gap=36),{'101'},W.ZERO);checked+=1
    assert not W.matches(frame(),{'111'},W.ZERO);checked+=1
    assert not W.matches(frame(effect=W.shift(W.ZERO,2,1)),{'101'},W.ZERO);checked+=1
    left,right=frame()
    mutations=[(((1,0,2),),right),
        (left,right[:-1]+(('box',('mark',0,W.ZERO)),)),
        (left,right[:-2]+((1,0,2),right[-1])),
        (left,right[:-3]+((0,2,37),)+right[-2:]),
        (left,right[:-3]+((1,1,37),)+right[-2:]),
        (left,right[:-3]+((0,1,-1),)+right[-2:])]
    for f in mutations:assert not W.matches(f,{'101'},W.ZERO);checked+=1
    return checked

def metadata_controls():
    checked=0
    normal=next(c for c in C.cases if c[3] is False and W.case_allowed(c[0],c[1]))
    haltcase=next(c for c in C.cases if c[3])
    p,b,t,_=normal
    rejected(lambda:W.run(C.T,p,b,t,halt=True));checked+=1
    hp,hb,ht,_=haltcase
    rejected(lambda:W.run(C.T,hp,hb,ht,halt=False));checked+=1
    rejected(lambda:W.run(C.T,p,b,t,allowed_pcs={'1'*100}));checked+=1
    rejected(lambda:W.run(C.T,hp,hb,ht,halt=True,allowed_pcs={''}));checked+=1
    wrong=W.canon([('b',1)],[('r',0,1,41),('b',1),('box',('plain',None))])
    rejected(lambda:W.run(C.T,p,b,wrong));checked+=1
    mutant=C.T.copy();w,d,_=mutant['96',int(p[0])]
    mutant['96',int(p[0])]=(w,d,'254')
    # Even artificial outgoing rows at the halting label must not allow an
    # early halt to be interpreted as an ordinary source block.
    mutant['254',0]=(0,'L','96');mutant['254',1]=(1,'L','96')
    rejected(lambda:W.run(mutant,p,b,t));checked+=1
    rejected(lambda:B.run(mutant,p,b,t));checked+=1
    return checked

def replay(checker):
    began=time.monotonic();n=0;excluded=0;rules=Counter();minimum=10**9
    for p,b,t,h in C.cases:
        if not checker.case_allowed(p,b):excluded+=1;continue
        r,literal=checker.run(C.T,p,b,t,halt=h,fuel=1000)
        n+=1;minimum=min(minimum,literal);rules.update(r)
    assert n==8385 and excluded==6
    assert rules['source_instructions']==n and rules.get('quiet_source_instructions',0)==0
    return dict(status='PASS',guarded_cases=n,excluded=excluded,
        minimum_literal_steps=minimum,rule_counts=dict(rules),seconds=time.monotonic()-began)

if __name__=='__main__':
    assert __debug__
    result=dict(status='PASS',offset_controls=offset_controls(),
        endpoint_controls=endpoint_controls(),metadata_controls=metadata_controls(),
        workspace_baseline=replay(W),workspace_quiet_baseline=replay(WB))
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=HERE.parent/'results/relaxed-affine-controls.json')
    args=ap.parse_args()
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
