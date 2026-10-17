#!/usr/bin/env python3
"""A small explicit port of the sound symbolic rules in M253.SymExec.

Unlike the upstream design prototype, this checker uses the Coq oracle's
single-effect box states, checks the register named by each decrement guard,
and records positive progress only for a literal transition. Each successful
run denotes all n>=0 and all register files satisfying its named guard.
The mark contract and three new prefix-carry contracts are the macro assumptions.
Requires at least one spare block. Inc appends [1]; positive dec grows gap by one.
Adapted from attributed source27 strict_affine.py; see ../sources/provenance.json.
"""
from collections import Counter


SKIP={'60':0,'44':1,'31':2,'56':3,'38':4,'40':5,'28':6,'64':7,'69':8}

def oracle(q,branch,state):
    # Each answer has an additional left-boundary cell count (0 or 1).
    # Modified contracts are proved in prefix_carry_lemmas.tex.
    if state==('plain',None) and q in SKIP:
        r=SKIP[q];return ('2' if r==0 else '6'),('mark',r),0
    if state[0]=='mark':
        r=state[1]
        if not 0<=r<9:return None
        if q=='73':return '48',('plain',('inc',r)),0
        if q=='95' and branch is not None and branch[0]==r:
            return ('112',('plain',None),0) if branch[1] else ('48',('plain',('dec',r)),1)
    return None

def canon_side(segs,left):
    out=[]
    for seg in segs:
        if seg[0]=='box':out.append(('box',seg[1]));continue
        b,a,c=(seg[1],0,1) if seg[0]=='b' else seg[1:]
        assert a>=0 and c>=0
        if (a,c)==(0,0):continue
        if out and out[-1][0]==b:out[-1]=(b,out[-1][1]+a,out[-1][2]+c)
        else:out.append((b,a,c))
    if left:
        while out and out[-1][0]==0:out.pop()
    return tuple(out)

def canon(left,right):return canon_side(left,True),canon_side(right,False)

def run(table,pc,branch,target,halt=False,fuel=20000):
    q='96';onleft=False;left=[('b',1)]
    right=[('b',int(b)) for b in pc]+[('r',0,1,40-len(pc)),('b',1),('box',('plain',None))]
    literal_steps=0;rule_count=Counter()
    for _ in range(fuel):
        if literal_steps>0:
            if halt and q=='254':return rule_count,literal_steps
            if not halt and not onleft and q=='96' and canon(left,right)==target:return rule_count,literal_steps
        if onleft:
            if not left:right=[('b',0)]+right;onleft=False;rule_count['pad_left']+=1;continue
            seg=left[0]
            if seg[0]=='b':left=left[1:];right=[seg]+right;onleft=False;rule_count['recenter']+=1;continue
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
        answer=oracle(q,branch,seg[1])
        if answer is not None:
            q,newstate,extra=answer;left=[('b',1)]*extra+left;right=[('box',newstate)];onleft=True;rule_count['box']+=1;continue
        write,move,following=table[q,0]
        assert write==0 and move=='L',('no justified box operation',q,branch,seg[1])
        q=following;onleft=True;literal_steps+=1;rule_count['literal_box_boundary']+=1
    raise AssertionError('symbolic fuel exhausted')
