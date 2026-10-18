#!/usr/bin/env python3
"""Checked deterministic source blocks, including arithmetic instructions.

Every branch must hold for every initial register vector in the named source
guard. A block stops before any undecidable decrement test, before CH, on a
repeated (source leaf, offset) pair, or at 32 instructions. Each output is a
positive-length source execution with an exact vector of primary offsets.
"""
from functools import lru_cache
import workspace_affine as A
from source_block_affine import source_step,lookup,site_map

@lru_cache(maxsize=None)
def endpoints(pc,branch=None,max_instructions=32):
    assert 1<=max_instructions<=256
    masks=A.initial_masks(pc,branch)
    leaf=pc;effect=A.ZERO;seen={(leaf,effect)};out=[]
    for count in range(1,max_instructions+1):
        _,op,r,_,_=site_map[leaf]
        if op=='CH':break
        guard=None
        if op=='CD':
            physical=A.PHYSICAL[r]
            low,high=A.offset_bounds(masks[physical],effect[physical])
            if high==0:guard=(physical,True)
            elif low>0:guard=(physical,False)
            else:break
            if count==1:assert guard==branch
        successor,delta,_,_=source_step(leaf,guard)
        assert successor is not None
        if delta is not None:
            kind,physical=delta
            effect=A.shift(effect,physical,1 if kind=='inc' else -1)
        leaf=lookup(successor)[0]
        assert leaf.rstrip('0')==successor.rstrip('0')
        assert leaf in A.source.INVARIANT
        out.append(dict(source_steps=count,successor_normalized=successor.rstrip('0'),
                        post_leaf=leaf,offset=effect))
        key=(leaf,effect)
        if key in seen:break
        seen.add(key)
    assert out or site_map[pc][1]=='CH'
    return tuple(out)
