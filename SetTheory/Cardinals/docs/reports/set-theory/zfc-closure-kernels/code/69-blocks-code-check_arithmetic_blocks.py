#!/usr/bin/env python3
"""Independent concrete and universal-atom audit of arithmetic source blocks.

The replay below reads the frozen tree directly and uses integer PC arithmetic
and matching-bit indices. It does not call source_step, lookup, full_inc, or
full_strip. Representative integer executions supplement, rather than replace,
the all-atoms guard checks and the mathematical offset induction.
"""
from pathlib import Path
from collections import Counter
import sys,json,time,argparse
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import arithmetic_blocks as G
import arithmetic_affine as X
import workspace_affine as W
if (HERE/'common.py').is_file():
    import common as C
    import program as P
else:
    import search_common as C
    import threshold_reachability as P

def direct_lookup(pc):
    node=0;path=''
    while True:
        bit=int(pc[len(path)]) if len(path)<len(pc) else 0
        path+=str(bit)
        op,arg=P.nodes[node][bit]
        if op!='CN':return path,op,arg
        node=arg

def increment(pc):
    if not pc:return ''
    return format((int(pc,2)+1)%(1<<len(pc)),f'0{len(pc)}b')

def strip(pc,bit,n):
    if n==0:return pc
    indices=[i for i in range(len(pc)-1,-1,-1) if pc[i]==bit]
    return pc[:indices[n-1]] if len(indices)>=n else ''

def direct_step(pc,physical_values):
    leaf,op,arg=direct_lookup(pc)
    values=list(physical_values);guard=None
    if op=='CH':raise AssertionError('CH crossed by a certified nonhalting block')
    if op in ('CI','CD'):
        r=P.audit.PHYSICAL[arg]
        if op=='CI':values[r]+=1;successor=increment(leaf)
        elif values[r]==0:
            guard=(r,True);successor=increment(strip(leaf,'0',1))
        else:
            guard=(r,False);values[r]-=1;successor=increment(leaf)
    elif op=='CB':successor=increment(strip(leaf,'0',arg))
    else:
        assert op=='CC'
        successor=strip(leaf,'1',arg)
    return successor.rstrip('0'),tuple(values),guard,op

def atom_values(mask,tail_value=4):
    return tuple(i for i in range(4) if mask&(1<<i))+((tail_value,) if mask&16 else ())

def universal_guard(mask,offset):
    # The infinite tail has lower endpoint4 and no finite upper endpoint.
    points=atom_values(mask)
    assert points and all(v+offset>=0 for v in points)
    is_zero=(not(mask&16) and all(v+offset==0 for v in points))
    is_positive=all(v+offset>0 for v in points)
    assert not(is_zero and is_positive)
    return True if is_zero else False if is_positive else None

def samples(masks):
    low=tuple(min(atom_values(m)) for m in masks)
    high=tuple(max(atom_values(m,67+r)) for r,m in enumerate(masks))
    mixed=tuple(low[r] if r%2==0 else high[r] for r in range(9))
    interior=tuple(atom_values(m,5)[r%len(atom_values(m,5))] for r,m in enumerate(masks))
    return tuple(dict.fromkeys((low,high,mixed,interior)))

def check_blocks():
    cases=targets=extra=0;replays=transitions=guard_checks=0;maximum=0;stops=Counter()
    for pc,branch,_,halt in C.cases:
        if not W.case_allowed(pc,branch):continue
        cases+=1;ends=G.endpoints(pc,branch)
        if halt:
            assert not ends and direct_lookup(pc)[1]=='CH'
            stops['CH_at_entry']+=1;continue
        assert ends and ends==G.endpoints(pc,branch,1)+ends[1:]
        assert [e['source_steps'] for e in ends]==list(range(1,len(ends)+1))
        targets+=len(ends);extra+=len(ends)>1;maximum=max(maximum,len(ends))
        masks=W.initial_masks(pc,branch)
        initial=samples(masks)
        # The first representative also audits every source guard atom-wise;
        # additional representatives exercise the concrete operation semantics.
        for sample_index,values in enumerate(initial):
            replays+=1;current=values;path=pc;old_offset=W.ZERO
            seen={(pc,W.ZERO)}
            for count,end in enumerate(ends,1):
                leaf,op,arg=direct_lookup(path)
                if sample_index==0:
                    for r,mask in enumerate(masks):
                        pts=atom_values(mask)
                        expected_low=min(pts)+old_offset[r]
                        expected_high=None if mask&16 else max(pts)+old_offset[r]
                        assert W.offset_bounds(mask,old_offset[r])==(expected_low,expected_high)
                    if op=='CD':
                        r=P.audit.PHYSICAL[arg]
                        selected=universal_guard(masks[r],old_offset[r])
                        assert selected is not None
                        assert selected==(current[r]==0)
                        if count==1:assert branch==(r,selected)
                        guard_checks+=1
                path,current,guard,actual_op=direct_step(path,current)
                transitions+=1
                assert actual_op==op and all(v>=0 for v in current)
                offset=tuple(a-b for a,b in zip(current,values))
                assert path==end['successor_normalized']
                assert direct_lookup(path)[0]==end['post_leaf']
                assert offset==end['offset'],(pc,branch,count,offset,end['offset'])
                assert all(a==b+d for a,b,d in zip(current,values,offset))
                old_offset=offset
                if count<len(ends):assert (end['post_leaf'],offset) not in seen
                seen.add((end['post_leaf'],offset))
            if sample_index==0:
                last=ends[-1];leaf,op,arg=direct_lookup(path)
                earlier={(pc,W.ZERO)}|{(e['post_leaf'],e['offset']) for e in ends[:-1]}
                if len(ends)==32:reason='cap'
                elif (leaf,old_offset) in earlier:reason='repeated_control_and_offset'
                elif op=='CH':reason='before_CH'
                else:
                    assert op=='CD'
                    r=P.audit.PHYSICAL[arg]
                    assert universal_guard(masks[r],old_offset[r]) is None
                    reason='undecidable_CD'
                stops[reason]+=1
    assert cases==8385
    return dict(admitted_cases=cases,endpoint_count=targets,cases_with_extra_endpoints=extra,
        maximum_source_steps=maximum,representative_integer_replays=replays,
        concrete_source_transitions=transitions,universal_atom_CD_checks=guard_checks,
        termination_reasons=dict(stops))

def rejected(f):
    try:f()
    except (AssertionError,KeyError):return
    raise AssertionError('negative control accepted')

def controls():
    n=0
    case=next(c for c in C.cases if not c[3] and W.case_allowed(c[0],c[1]) and len(G.endpoints(c[0],c[1]))>1)
    pc,b,t,_=case;end=G.endpoints(pc,b)[-1];p=end['successor_normalized'];offset=end['offset']
    keys={(p,offset):end['source_steps']}
    def frame(path=p,effect=offset,growth=0):
        return X.canon([('b',1)],[('b',int(x)) for x in path]+
            [('r',0,1,40-len(path)+growth),('b',1),('box',('plain',effect))])
    assert X.matches(frame(),keys);n+=1
    assert X.matches(frame(growth=11),keys);n+=1
    assert not X.matches(frame(effect=W.shift(offset,0,1)),keys);n+=1
    assert not X.matches(frame(path='1'*39),keys);n+=1
    assert not X.matches(frame(growth=-1),keys);n+=1
    rejected(lambda:G.endpoints(pc,b,0));n+=1
    rejected(lambda:G.endpoints(pc,b,257));n+=1
    rejected(lambda:X.run(C.T,pc,b,t,halt=True));n+=1
    hp,hb,ht,_=next(c for c in C.cases if c[3])
    rejected(lambda:X.run(C.T,hp,hb,ht,halt=False));n+=1
    mutant=C.T.copy();w,d,_=mutant['96',int(pc[0])]
    mutant['96',int(pc[0])]=(w,d,'254')
    mutant['254',0]=(0,'L','96');mutant['254',1]=(1,'L','96')
    rejected(lambda:X.run(mutant,pc,b,t));n+=1
    original=X.endpoints
    try:
        bad=dict(end,source_steps=0)
        X.endpoints=lambda *_:(bad,)
        rejected(lambda:X.run(C.T,pc,b,t));n+=1
    finally:X.endpoints=original
    return n

def baseline():
    n=0;minimum=10**9;rules=Counter()
    for pc,b,t,h in C.cases:
        if not X.case_allowed(pc,b):continue
        r,literal=X.run(C.T,pc,b,t,halt=h,fuel=1000)
        n+=1;minimum=min(minimum,literal);rules.update(r)
    assert n==8385 and rules['source_instructions']==n
    return dict(status='PASS',guarded_cases=n,minimum_literal_steps=minimum,rule_counts=dict(rules))

if __name__=='__main__':
    assert __debug__
    began=time.monotonic()
    result=dict(status='PASS',blocks=check_blocks(),mutation_controls=controls(),baseline=baseline())
    result['seconds']=time.monotonic()-began
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=HERE.parent/'results/arithmetic-block-controls.json')
    args=ap.parse_args()
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
