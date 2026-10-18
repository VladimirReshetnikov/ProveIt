#!/usr/bin/env python3
"""Sufficient symbolic checker modulo unused workspace.

New layer: any finite sequence of unchanged register macros may be used.
It records the exact affine offset of each of the nine primary registers,
proves all decrement guards from the checked source invariant, and permits
extra appended spare blocks and extra nonnegative separator space.

The tape rewrite engine is adapted from the attributed context246
prefix_affine.py / source27 checker. This is an ordinary mathematical
certificate checker, not a proof-assistant kernel.
"""
from collections import Counter
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'code'))
import source_exactroot_affine as source
from source_exactroot_block_affine import endpoints
from source_block_affine import site_map

canon=source.canon
case_allowed=source.case_allowed
PHYSICAL=source.PHYSICAL
SKIP=source.SKIP
ZERO=(0,)*9

def initial_masks(pc,branch):
    assert case_allowed(pc,branch),('excluded source guard',pc,branch)
    masks=[0]*9
    for logical,physical in enumerate(PHYSICAL):
        masks[physical]=source.INVARIANT[pc][logical]
    if branch is not None:
        r,zero=branch
        masks[r]&=1 if zero else ~1
    assert all(0<m<32 for m in masks)
    return tuple(masks)

def offset_bounds(mask,offset):
    """Image of a K=4 mask after adding an exact integer offset."""
    atoms=[i for i in range(5) if mask&(1<<i)]
    low=min(atoms)+offset
    high=None if mask&16 else max(atoms)+offset
    assert low>=0,('unproved nonnegative register',mask,offset)
    return low,high

def shift(effect,r,delta):
    out=list(effect);out[r]+=delta;return tuple(out)

def oracle(q,state,masks):
    if state[0]=='plain' and q in SKIP:
        effect=ZERO if state[1] is None else state[1]
        assert len(effect)==9
        r=SKIP[q]
        return ('2' if r==0 else '6'),('mark',r,effect),0
    if state[0]!='mark':return None
    _,r,effect=state
    assert 0<=r<9 and len(effect)==9
    if q=='73':
        # The inherited increment appends a spare 1. The abstraction forgets
        # its count, but not the nine primary values or file boundary.
        return '48',('plain',shift(effect,r,1)),0
    if q=='95':
        low,high=offset_bounds(masks[r],effect[r])
        if high==0:return '112',('plain',effect),0
        if low>0:return '48',('plain',shift(effect,r,-1)),1
        # Both branches are possible. No speculative choice is permitted.
        return None
    return None

def frame_parts(frame):
    """Parse a canonical frame, retaining its actual affine gap constant."""
    left,right=frame
    if left!=((1,0,1),) or len(right)<3:return None
    box=right[-1]
    if box[0]!='box' or box[1][0]!='plain':return None
    if right[-2]!=(1,0,1):return None
    gap=right[-3]
    if len(gap)!=3 or gap[:2]!=(0,1) or gap[2]<0:return None
    bits=[]
    for run in right[:-3]:
        if len(run)!=3 or run[0] not in (0,1) or run[1]!=0:return None
        if not 0<run[2]<=40:return None
        bits.append(str(run[0])*run[2])
    pc=''.join(bits)
    if pc.endswith('0'):return None
    if len(pc)+gap[2]<40:return None
    return pc,gap[2],box[1][1]

def expected_offset(effect):
    if effect is None:return ZERO
    kind,r=effect
    assert kind in ('inc','dec') and 0<=r<9
    return shift(ZERO,r,1 if kind=='inc' else -1)

def target_spec(target):
    parts=frame_parts(target)
    assert parts is not None,('invalid reference target',target)
    pc,_,effect=parts
    return frozenset((pc,)),expected_offset(effect)

def matches(frame,allowed_pcs,expected):
    parts=frame_parts(frame)
    if parts is None:return False
    pc,_,effect=parts
    if effect is None:effect=ZERO
    return pc in allowed_pcs and effect==expected

def run(table,pc,branch,target,halt=False,fuel=20000,allowed_pcs=None):
    masks=initial_masks(pc,branch)
    assert halt==(site_map[pc][1]=='CH'),('incorrect source halting metadata',pc,halt)
    if not halt:
        ends=endpoints(pc,branch)
        assert ends and target==ends[0]['affine_target'],('wrong immediate source target',pc,branch)
        certified_steps={}
        for end in ends:
            assert end['source_steps']>=1
            certified_steps.setdefault(end['successor_normalized'],end['source_steps'])
        pcs,expected=target_spec(target)
        if allowed_pcs is not None:
            pcs=frozenset(allowed_pcs)
            assert pcs and pcs<=certified_steps.keys(),('uncertified quiet source endpoint',pc,pcs)
    else:
        assert allowed_pcs is None,('quiet endpoint set supplied for CH',pc)
    q='96';onleft=False;left=[('b',1)]
    right=[('b',int(b)) for b in pc]+[('r',0,1,40-len(pc)),('b',1),('box',('plain',None))]
    literal_steps=0;rule_count=Counter()
    for _ in range(fuel):
        if q=='254':
            assert halt and literal_steps>0,('unexpected halt in nonhalting source block',pc,branch)
            rule_count['source_instructions']+=1
            return rule_count,literal_steps
        if literal_steps>0:
            if not halt and not onleft and q=='96' and matches(canon(left,right),pcs,expected):
                endpoint_pc=frame_parts(canon(left,right))[0]
                steps=certified_steps[endpoint_pc]
                rule_count['source_instructions']+=steps
                rule_count['quiet_source_instructions']+=steps-1
                return rule_count,literal_steps
        if onleft:
            if not left:
                right=[('b',0)]+right;onleft=False;rule_count['pad_left']+=1;continue
            seg=left[0]
            if seg[0]=='b':
                left=left[1:];right=[seg]+right;onleft=False;rule_count['recenter']+=1;continue
            assert seg[0]=='r','box cannot occur on the left'
            _,b,a,c=seg;write,move,following=table[q,b]
            if move=='L' and following==q:
                left=left[1:];right=[('r',write,a,c)]+right;rule_count['scan_left']+=1;continue
            if c>0:
                left=[('b',b),('r',b,a,c-1)]+left[1:];rule_count['peel_left']+=1;continue
            if a==0:left=left[1:];rule_count['empty_left']+=1;continue
            raise AssertionError(('unknown left-run length',q,a,c))
        assert right,'right exterior has no rule'
        seg=right[0]
        if seg[0]=='b':
            write,move,following=table[q,seg[1]];q=following;literal_steps+=1;rule_count['literal']+=1
            if move=='R':left=[('b',write)]+left;right=right[1:]
            else:right=[('b',write)]+right[1:];onleft=True
            continue
        if seg[0]=='r':
            _,b,a,c=seg;write,move,following=table[q,b]
            if move=='R' and following==q:
                left=[('r',write,a,c)]+left;right=right[1:];rule_count['scan_right']+=1;continue
            if c>0:
                right=[('b',b),('r',b,a,c-1)]+right[1:];rule_count['peel_right']+=1;continue
            if a==0:right=right[1:];rule_count['empty_right']+=1;continue
            raise AssertionError(('unknown right-run length',q,a,c))
        assert seg[0]=='box' and len(right)==1
        answer=oracle(q,seg[1],masks)
        if answer is not None:
            if q=='73':rule_count['increment_box']+=1
            if q=='95':rule_count['decrement_box']+=1
            q,newstate,extra=answer
            left=[('b',1)]*extra+left;right=[('box',newstate)]
            onleft=True;rule_count['box']+=1;continue
        write,move,following=table[q,0]
        assert write==0 and move=='L',('no justified box operation',q,branch,seg[1])
        q=following;onleft=True;literal_steps+=1;rule_count['literal_box_boundary']+=1
    raise AssertionError('symbolic fuel exhausted')
